-- Prove2me | Theorems.Thm_KruskalAnalysis_call_contract
-- name    : KruskalAnalysis.call_contract
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-11T00:06:57.604308+00:00
-- url     : https://prove2.me/theorems/3dcc5a79-2076-49d6-8193-a020427afbe0
-- title:
--   Kruskal: reusable correctness and inverse-Ackermann running time
-- statement:
--   For allocated source, target and weight arrays with nonnegative counts $V,E$ and endpoints in $[0,V)$, there exist one final heap, fresh valid flag-array reference and selected-edge list such that the actual `kruskal.Call` terminates and the selected edges form a minimum spanning forest. Every flag is exactly 0 or 1 according to edge-id membership; flags outside the input range are zero. All previously allocated caller sequences, objects and collections are preserved. The three input arrays may alias.
--
--   The very same call supplies exact increments of every clock and satisfies
--   $$
--   T=\operatorname{runtime}(\operatorname{Heap.cost}(before,after))\le B(V,E).
--   $$
--   Initial counters may be nonzero. No unproved data-structure correctness or runtime assumption is supplied by the client. Reuse this `Call` theorem inside a later algorithm to keep correctness, storage, allocation and costs together. The value-only `correct` and `running_time` theorems are corollaries.
--
--   For $V$ vertices and $E$ edges, define
--   $$
--   B(V,E)=2E\bigl(3\lfloor\log_2(E+1)\rfloor+2\bigr)+V+2+E\bigl(10\alpha(V)+14\bigr).
--   $$
--   The eight unit-weight clocks are `sort_steps`, `heap_comparisons`, `heap_swaps`, `uf_init`, `uf_find`, `uf_compress`, `uf_union`, and `kruskal`. Their sum is `KruskalAnalysis.runtime`; the displayed expression is `KruskalAnalysis.runtimeBound`. Thus the finite inequality has scale $O(V+E\log(E+1)+E\alpha(V))$. The inverse-Ackermann improvement is in the disjoint-set term; sorting still costs $O(E\log(E+1))$.
--
--   Here $n$ is the fixed number of elements, $\alpha(n)$ is `Algo2Lean.Ackermann.alpha`, and $\Phi$ is `Algo2Lean.UnionFind.potential`. Their definitions are in the separate Ackermann and union-find amortization definition bundles. The inverse is the least positive $k$ with $A_k(1)>n$, where $A_0(r)=r+1$ and $A_{k+1}(r)$ iterates $A_k$ exactly $r+1$ times starting at $r$.
--
--   Costs count the named source ticks over mathematical integers and total integer-indexed sequences. They are not wall-clock time, bit complexity, or a count of every arithmetic operation, access, allocation, or compiler transition. Counters may start at arbitrary values; bounds refer to the increments during this call.
--
--   Part of the [Algo2Lean](https://www.algo2lean.com/) CLRS series: *Introduction to Algorithms*, fourth edition, Chapter 21, §21.2 (Kruskal), the safe-edge principle in Theorem 21.1 (§21.1), and the union-by-rank/path-compression bound in Theorem 19.14 (§19.4).
--
--   The `.algo` code closely follows the textbook pseudocode: initialize the
--   empty selection and singleton components, sort edges by weight, then compare
--   endpoint representatives before selecting an edge and joining its components.
--   Edge identifiers and flags represent sets, the constructor performs the
--   make-set loop, and an independently verified sorter supplies the abstract
--   sorting operation. Full path compression and union by rank remain in the
--   independently analyzed data structure; the runtime includes the explicit
--   finds and the finds performed inside accepted unions.
--
--   ## Algorithm source
--
--   Project import root: `examples/kruskal`. Entry file: `kruskal.algo`.
--
--   ### `union_find.algo`
--
--   ```python
--   # Disjoint sets over the integer elements 0, ..., size - 1.
--   # Each root names one component. Union by rank bounds parent paths, and
--   # find compresses every visited path directly to its root.
--   # Clients must pass in-range elements. The representation is independent
--   # of graphs, edge weights, or any particular client algorithm.
--
--   class UnionFind:
--       parent: Seq
--       rank: Seq
--       size: Int
--
--       def __init__(self, size: Int) -> None:
--           # Batch the CLRS MAKE-SET operation for all elements in [0, size).
--           self.parent = const(0)
--           self.rank = const(0)
--           self.size = size
--           vertex = 0
--           tick("uf_init")
--           # @initialize
--           while vertex < size:
--               self.parent[vertex] = vertex
--               vertex += 1
--               tick("uf_init")
--
--       def find(self, vertex: Int) -> Int:
--           # CLRS FIND-SET: recursion finds the root, then rewrites every parent
--           # along the return path. This is full path compression, not path halving.
--           parent = self.parent
--           tick("uf_find")
--           # @follow
--           if parent[vertex] == vertex:
--               return vertex
--           root = self.find(parent[vertex])
--           # @compress
--           parent[vertex] = root
--           tick("uf_compress")
--           return root
--
--       def union(self, a: Int, b: Int) -> Bool:
--           # CLRS UNION: find both roots, then apply union by rank (LINK).
--           # The Boolean result reports whether two components were joined.
--           left = self.find(a)
--           right = self.find(b)
--           tick("uf_union")
--           if left == right:
--               return False
--           # @link
--           if self.rank[left] < self.rank[right]:
--               self.parent[left] = right
--           elif self.rank[right] < self.rank[left]:
--               self.parent[right] = left
--           else:
--               # Equal ranks may choose either root; here the left root wins.
--               self.parent[right] = left
--               self.rank[left] = self.rank[left] + 1
--           return True
--   ```
--
--   ### `indexed_heap.algo`
--
--   ```python
--   # An indexed binary min-heap for Dijkstra's priority queue.
--   # vertices[position] and positions[vertex] are inverse on the active prefix.
--   # keys is indexed by vertex; position -1 means the vertex is not in the heap.
--   # Clients use nonnegative vertex identifiers, so pop_min can use -1 for empty.
--
--   class MinHeap:
--       vertices: Seq
--       positions: Seq
--       keys: Seq
--       size: Int
--
--       def __init__(self) -> None:
--           self.vertices = const(0)
--           self.positions = const(-1)
--           self.keys = const(0)
--           self.size = 0
--
--       def swap(self, i: Int, j: Int) -> None:
--           a = self.vertices[i]
--           b = self.vertices[j]
--           # @exchange
--           self.vertices[i] = b
--           self.vertices[j] = a
--           self.positions[a] = j
--           self.positions[b] = i
--           tick("heap_swaps")
--
--       def sift_up(self, i: Int) -> None:
--           # @up_loop
--           while i > 0:
--               parent = (i - 1) // 2
--               tick("heap_comparisons")
--               if self.keys[self.vertices[parent]] <= self.keys[self.vertices[i]]:
--                   return
--               self.swap(i, parent)
--               i = parent
--
--       def sift_down(self, i: Int) -> None:
--           # @down_loop
--           while 2 * i + 1 < self.size:
--               child = 2 * i + 1
--               right = child + 1
--               if right < self.size:
--                   tick("heap_comparisons")
--                   if self.keys[self.vertices[right]] < self.keys[self.vertices[child]]:
--                       child = right
--               # @compare_child
--               tick("heap_comparisons")
--               if self.keys[self.vertices[i]] <= self.keys[self.vertices[child]]:
--                   return
--               self.swap(i, child)
--               i = child
--
--       def push_or_decrease(self, vertex: Int, key: Int) -> None:
--           i = self.positions[vertex]
--           if i < 0:
--               self.keys[vertex] = key
--               i = self.size
--               self.vertices[i] = vertex
--               self.positions[vertex] = i
--               self.size += 1
--               self.sift_up(i)
--           else:
--               tick("heap_comparisons")
--               if key < self.keys[vertex]:
--                   self.keys[vertex] = key
--                   self.sift_up(i)
--
--       def pop_min(self) -> Int:
--           if self.size <= 0:
--               return -1
--           vertex = self.vertices[0]
--           last = self.size - 1
--           self.swap(0, last)
--           self.size = last
--           self.positions[vertex] = -1
--           if last > 0:
--               self.sift_down(0)
--           return vertex
--
--       def is_empty(self) -> Bool:
--           return self.size <= 0
--   ```
--
--   ### `sort_indices.algo`
--
--   ```python
--   # Order the identifiers [0, count) by their keys using a reusable binary heap.
--   # This supplies Kruskal's sort-by-weight step: insert every identifier, then
--   # extract minima. It is not the in-place HEAPSORT procedure from CLRS Chapter 6.
--   # Only identifiers are reordered; keys are unchanged. Equal-key identifiers
--   # may appear in either order.
--   from indexed_heap import MinHeap
--
--
--   def sort_indices(keys: Seq, count: Int) -> Seq:
--       queue = MinHeap()
--       result = const(0)
--       index = 0
--       # @insert
--       while index < count:
--           tick("sort_steps")
--           queue.push_or_decrease(index, keys[index])
--           index += 1
--       index = 0
--       # @extract
--       while index < count:
--           tick("sort_steps")
--           result[index] = queue.pop_min()
--           index += 1
--       return result
--   ```
--
--   ### `kruskal.algo`
--
--   ```python
--   # Minimum spanning forest by CLRS MST-KRUSKAL (fourth edition, Section 21.2).
--   # Edge identifiers are 0, ..., count - 1; endpoint arrays contain vertices
--   # in 0, ..., size - 1. The zero/one flag sequence represents the edge set A.
--   from union_find import UnionFind
--   from sort_indices import sort_indices
--
--
--   def kruskal(size: Int, sources: Seq, targets: Seq, weights: Seq, count: Int) -> Seq:
--       chosen = const(0)
--       # Construct one singleton set for each vertex (the textbook MAKE-SET loop).
--       sets = UnionFind(size)
--       order = sort_indices(weights, count)
--       index = 0
--       tick("kruskal")
--       # @scan
--       while index < count:
--           edge = order[index]
--           a = sources[edge]
--           b = targets[edge]
--           tick("kruskal")
--           left = sets.find(a)
--           right = sets.find(b)
--           # @test
--           if left != right:
--               # @select
--               chosen[edge] = 1
--               # @join
--               sets.union(a, b)
--           index += 1
--       return chosen
--   ```
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/kruskal.lean#L164-L182

import Definitions.Def_Algo_kruskal_Analysis
import Theorems.Thm_KruskalAnalysis_call_complete

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem KruskalAnalysis.call_contract :
    ∀ (heap : Algo2LeanGenerated.Heap) (size count : Int)
      (sources targets weights : Algo2LeanGenerated.SeqRef),
      Algo.kruskal.kruskal.ValidInput heap
          (Prod.mk.{0, 0} size
            (Prod.mk.{0, 0} sources (Prod.mk.{0, 0} targets (Prod.mk.{0, 0} weights count)))) →
        KruskalInput.WellFormed size count (heap.read sources) (heap.read targets) →
          Exists.{1} fun final =>
            Exists.{1} fun chosen =>
              Exists.{1} fun selected =>
                Algo.kruskal.kruskal.Call heap
                    (Prod.mk.{0, 0} size
                      (Prod.mk.{0, 0} sources (Prod.mk.{0, 0} targets (Prod.mk.{0, 0} weights count))))
                    final chosen ∧
                  Algo2Lean.Kruskal.MinimumSpanningForest
                      (KruskalInput.edges (heap.read sources) (heap.read targets) (heap.read weights)
                        count)
                      selected ∧
                    KruskalAnalysis.Flags (final.read chosen) selected ∧
                      heap.Footprint final List.nil.{0} List.nil.{0} List.nil.{0} ∧
                        LE.le.{0} heap.nextRef chosen ∧
                          LT.lt.{0} chosen final.nextRef ∧
                            heap.Increments final (heap.cost final) ∧
                              LE.le.{0} (KruskalAnalysis.runtime (heap.cost final))
                                (KruskalAnalysis.runtimeBound size.toNat count.toNat) := by
  sorry
