-- Prove2me | Theorems.Thm_MultiplierAssoc206_Resolution_lemma_7_3
-- name    : MultiplierAssoc206.Resolution.lemma_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:15:00.636326+00:00
-- url     : https://prove2.me/theorems/1041d782-b073-4bc4-8cc2-cb3e84524ebb
-- title:
--   Construction of index maps with $n_0=O(m^4\log m)$
-- statement:
--   There is an absolute constant $C$ such that for every $m\in\mathbb N$ there is an integer
--   $$n_0\le C\,m^4\log(m+1)$$
--   with the following property. For every bipartite graph $H=(U,V,E)$ with $|U|=m+1$ and $|V|=m$, and $g=\lceil\log_2(m+2)\rceil+2$, there are maps $i:U\to\mathbb N$, $j:E\to\mathbb N$, $k:V\to\mathbb N$ and columns $\mathrm{col}_{\mathbf{xy}}(v)$, $\mathrm{col}_{\mathbf{yz}}(u)$, $K$ satisfying:
--
--   1. (Mapping pattern) $i,j,k$ map injectively to multiples of $g$, and $i(u)+j(e)+k(v)<n_0$ for all $u\in U$, $e\in E$, $v\in V$.
--   2. (Inner collision pattern) (a) for each $v\in V$ the incident pairs $(u_e,e)$, $e\in E(v)$, share the column $\mathrm{col}_{\mathbf{xy}}(v)=i(u_e)+j(e)$; distinct $v$ give distinct columns; each non-incident pair $(u,e)$ has a column $i(u)+j(e)$ different from that of every other pair. (b) Symmetrically for the pairs $(e,v_e)$, $e\in E(u)$, and the columns $\mathrm{col}_{\mathbf{yz}}(u)=j(e)+k(v_e)$.
--   3. (Outer collision pattern) two triples $(u,e,v)$ have the same column $i(u)+j(e)+k(v)$ if and only if they have the same difference pair $\big(i(u)-i(u_e),k(v)-k(v_e)\big)$; (a) the difference pair is $(0,0)$ exactly for the incident triples $(u_e,e,v_e)$, whose common column is $K$; (b) if $i(u)-i(u_e)=i(u')-i(u_{e'})\ne0$ then $(u,u_e)=(u',u_{e'})$, and if $k(v)-k(v_e)=k(v')-k(v_{e'})\ne0$ then $(v,v_e)=(v',v_{e'})$.
--
--   The maps embed the graph into the input bit-vectors so that the four multipliers see exactly the perfect-matching constraints.
--
--   Differences from the source:
--   - encoding: n₀ = O(m⁴ log m) → n₀ ≤ C m⁴ log(m+1) with one absolute C (natural logarithm), for every m ≥ 0; reason: log(m+1) ≤ 2 log m for m ≥ 2, so the bound is O(m⁴ log m); log(m+1) avoids the value log 1 = 0 at m = 1
--   - generalization: for H there is an integer n₀ and maps → n₀ depends only on m and is chosen before the graph; reason: the source's proof gives n₀ = 4K with K = 2g(B+1)M depending on m only; a uniform n₀ specializes to the per-graph statement
--   - reading: g = ⌈log(m+2)⌉ + 2 → g = ⌈log₂(m+2)⌉ + 2 (Nat.clog 2 (m+2) + 2); reason: the proof of Lemma 7.5(ii) uses 2^{g−1} ≥ 2(m+2), which needs base 2
--   - reading: each non-incident pair occupies its own column; the column depends only on the difference pair and distinct pairs map to distinct columns → the non-incident pair's column differs from the column of every other pair, incident or not; equal outer columns if and only if equal difference pairs; reason: plain reading of both sentences
--   - encoding: the columns col_xy(v), col_yz(u) and K are denoted by the lemma → they are data of the structure with the stated properties; injectivity of v ↦ col_xy(v) is required on all of V; reason: for a vertex with edges the column is determined by the edges; a vertex without edges does not occur in §§7–8, and any injective choice exists there; differences are computed in ℤ
--   - generalization: the standing graph assumptions of §5 include a constant degree bound and no isolated vertices → all finite simple bipartite graphs with the stated part cardinalities, including isolated vertices and m = 0; reason: the index-map construction uses only injections of vertices into the marks and the simple edge set, not the degree bound or absence of isolated vertices; at m = 0 the edge and V types are empty and n₀ = 0 works
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF pp.15–16 (printed pp.14–15), Lemma 7.3

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_IndexMaps

namespace MultiplierAssoc206.Resolution

/-- Lemma 7.3 (Construction of index maps), PDF pp.15–16 (printed pp.14–15): with
`g = ⌈log₂(m+2)⌉ + 2`, maps with properties (i)–(iii) exist for some `n₀ = O(m⁴ log m)`;
here `n₀ ≤ C m⁴ log(m+1)` with one absolute `C`, and `n₀` depends only on `m`. -/
theorem lemma_7_3 :
    ∃ C : ℝ, ∀ m : ℕ, ∃ n₀ : ℕ, (n₀ : ℝ) ≤ C * (m : ℝ) ^ 4 * Real.log ((m : ℝ) + 1) ∧
      ∀ (U V : Type) [Fintype U] [Fintype V], Fintype.card U = m + 1 → Fintype.card V = m →
        ∀ E : Finset (U × V), Nonempty (IndexMaps E (stripWidth m) n₀) := by sorry

end MultiplierAssoc206.Resolution
