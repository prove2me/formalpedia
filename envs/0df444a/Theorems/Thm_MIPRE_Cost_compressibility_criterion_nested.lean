-- Prove2me | Theorems.Thm_MIPRE_Cost_compressibility_criterion_nested
-- name    : MIPRE.Cost.compressibility_criterion_nested
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:26:39.241982+00:00
-- url     : https://prove2.me/theorems/43599427-3965-483a-b28f-73d2ee2b31da
-- title:
--   Nested compressibility criterion ($B_0 \subseteq B_1$): class-preserving compression yields a halting reduction
-- statement:
--   Throughout, computation is in the ambient cost model of the formalization: programs (`Prog`) form a small first-order language on binary-tree data (`Data`), $\mathrm{size}$ counts the nodes of a value, a bit string $x \in \{0,1\}^*$, a natural number (in binary) or a pair is a value through a size-faithful encoding $\mathrm{encode}$, and a program is its own tree encoding, of size $|e|$. The timed semantics charges one unit per evaluation rule plus the size of every value read, so a run of cost $t$ has output of size at most $t$. A polynomial-time computable function (`PolyTimeFun α β`) is a function together with a closed program computing it on encodings and an explicit polynomial bounding the cost in the size of the encoded input. "$e$ halts on the empty input" means that the program $e$, run on the value `nil`, halts (`Halts e nil`). The pair $(c, m)$ of a program and a parameter is a succinct description of $x \in \{0,1\}^*$ (`IsSuccinctDesc c m x`) when $c$ is closed, $|x| \le 2^m$, and for every $k \in \mathbb{N}$ the program $c$ on the binary input $k$ answers the bit query, returning the $k$-th bit of $x$ if $k < |x|$ and the marker $2$ otherwise, within cost $(m+1)(\ell(k)+1)^2$, where $\ell(k)$ denotes the binary length of $k$. We write $\ell(n)$ for the binary length of $n$ and $|c|$ for the size of a program.
--
--   Let $A, B_0, B_1 : \mathbb{N} \to \mathcal{P}(\{0,1\}^*)$ be families of languages indexed by a level $n$, with $B_0(n) \subseteq B_1(n)$ for all $n$, and let $n_0 \in \mathbb{N}$. Suppose:
--
--   1. there are strings $y_{\mathrm{yes}}, y_{\mathrm{no}}$ with $y_{\mathrm{yes}} \in A(n)$ and $y_{\mathrm{no}} \in B_0(n)$ for every $n \ge n_0$;
--   2. there is a closed program $S$ (well-scoped in one variable) semideciding the complement of $B_1$ uniformly in the level: for all $x \in \{0,1\}^*$ and $n$, $S$ halts on $\mathrm{encode}((x, n))$ if and only if $x \notin B_1(n)$;
--   3. there is a polynomial-time computable $\mathrm{Compr} : \mathrm{Prog} \times \mathbb{N} \to \{0,1\}^*$ such that for all $c$, $x$ and $n \ge n_0$ with $2|c| \le n$, $(c, n)$ a succinct description of $x$ and $|x| \le n+1$, writing $y = \mathrm{Compr}(c, n)$: if $x \in A(2n+1)$ then $y \in A(n)$, and if $x \in B_0(2n+1)$ then $y \in B_0(n)$.
--
--   Then there are a polynomial-time computable $g : \mathrm{Prog} \to \{0,1\}^*$ and a constant $K \in \mathbb{N}$ such that, with $r(e) = 2^{K+1+|e|}$,
--
--   $$ \forall e \in \mathrm{Prog}:\quad n_0 \le r(e)\ \wedge\ \bigl(e \text{ halts on the empty input} \Rightarrow g(e) \in A(r(e))\bigr)\ \wedge\ \bigl(e \text{ does not halt on the empty input} \Rightarrow g(e) \in B_1(r(e))\bigr). $$
--
--   This is the form of Lin's compressibility criterion that the $\mathrm{coRE}$ direction of $\mathrm{MIP}^{\mathrm{co}} = \mathrm{coRE}$ needs: there $A$ is the class of small commuting-operator value, $B_0$ the class of the main theorem (a perfect PCC strategy, preserved by the completeness of compression) and $B_1$ the class of commuting-operator value $1$, whose complement the upper semidecider recognizes and which no compression theorem preserves. The case $B_0 = B_1$ is `compressibility_criterion_levels`, from which the level-free criterion `compressibility_criterion` and its Mathlib form `compressibility_criterion_halting` follow; the whole proof lives here. The level bookkeeping is what an instantiation by gap-preserving compression needs: the compressor runs in time polynomial in the *size* of its input $(c, n)$, i.e. polylogarithmic in $n$, while a single bit query to $c$ costs up to $n$, so it cannot read the string $x$ it compresses and can only embed $c$ into its output for a later reader whose budget is polynomial in $n$ (the decider of a game at index $n$); the slack $2|c| \le n$ keeps that output short, and the hypothesis relates the class of $x$ at level $2n+1$ to the class of the output at level $n$, which is exactly what the proof uses, the self-referential decider at level $n$ compressing the string it itself computes at level $2n+1$. The condition $|x| \le n+1$ is not an extra demand on $\mathrm{Compr}$ but a weakening of what it must cover: the described string is the output of a run whose cost the threshold bounds by $n+1$.
--
--   **Formalization Note**. The statement is `MIPRE.Cost.compressibility_criterion_nested`, with `Compr : PolyTimeFun (Prog × ℕ) BitStr` (the succinctness parameter of the description is the level itself), the semidecider hypothesis `hS` an equivalence `Halts S (encode (x, n)) ↔ x ∉ B₁ n` (both directions are used), and the conclusion `∃ g K, ∀ e, n₀ ≤ 2 ^ (K + 1 + esize e) ∧ (Halts e .nil → g e ∈ A (2 ^ (K + 1 + esize e))) ∧ (¬ Halts e .nil → g e ∈ B₁ (2 ^ (K + 1 + esize e)))`. The halting problem is that of the ambient model's programs on the input `nil`. Three departures from the paper's statement and proof are recorded in the module docstring of `MIPRE/Foundations/Compression.lean`. (i) *Succinctness time bound*: [MNY, Definition 2.4] requires the runtime of the description on every query $k$ to be at most $n$; in a model that charges for reading its input this is vacuous for $\ell(k) > n$, so the formalization requires $(n+1)(\ell(k)+1)^2$ instead, the quadratic factor in $\ell(k)$ being what the bit-indexing program `bitAtProg` achieves (each zero test and decrement of the binary index copies it); any fixed polynomial in $n$ and $\ell(k)$ would do, provided the compression theorem for games uses the same one. (ii) *The next level is $2n+1$, not $n+1$*: incrementing a binary numeral needs a carry propagation, prepending a one bit is a single node (`PolyTimeFun.next`); the levels $n, 2n+1, 4n+3, \dots$ still grow without bound and $\ell(2n+1) = \ell(n)+1$ keeps every overhead polynomial in $|e| + \ell(n)$. (iii) *The threshold is explicit*: $r(e) = 2^{K+1+|e|}$ for a constant $K$ obtained from the overhead polynomial by the threshold lemma `exists_threshold` (above it, a polynomial in $|e| + \ell(n)$ is at most $n+1$), and it is computed in polynomial time by `PolyTimeFun.threshold K`. In addition, the start level of the recursion is carried as data next to the current level (the decider's input is $(c', (e, (m, n)))$), so that the decider's code does not depend on the threshold, which is chosen afterwards from the decider's time bound.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Compression.lean#L456-L770; blueprint lem:compressible-criterion-nested, https://vidick.github.io/MIPRE-formalization/blueprint/; [Lin25] J. Lin, MIP^co = coRE, Proc. 58th STOC, 2026, arXiv:2510.07162, the compression criterion for RE-complete problems (direction "weakly compressible implies RE-complete"), in the succinct-description formulation of [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Compression

open MIPRE
open MIPRE.Cost
open Polynomial

theorem MIPRE.Cost.compressibility_criterion_nested
    (A B₀ B₁ : ℕ → Set BitStr) (n₀ : ℕ) (hsub : ∀ n, B₀ n ⊆ B₁ n)
    (yYes : BitStr) (hyes : ∀ n, n₀ ≤ n → yYes ∈ A n)
    (yNo : BitStr) (hno : ∀ n, n₀ ≤ n → yNo ∈ B₀ n)
    (S : Prog) (hSws : S.WellScoped 1)
    (hS : ∀ (x : BitStr) (n : ℕ), Halts S (encode (x, n)) ↔ x ∉ B₁ n)
    (Compr : PolyTimeFun (Prog × ℕ) BitStr)
    (hCompr : ∀ (c : Prog) (x : BitStr) (n : ℕ), n₀ ≤ n → 2 * esize c ≤ n →
      IsSuccinctDesc c n x → x.length ≤ n + 1 →
        (x ∈ A (2 * n + 1) → Compr (c, n) ∈ A n) ∧ (x ∈ B₀ (2 * n + 1) → Compr (c, n) ∈ B₀ n)) :
    ∃ (g : PolyTimeFun Prog BitStr) (K : ℕ),
      ∀ e : Prog, n₀ ≤ 2 ^ (K + 1 + esize e) ∧
        (Halts e .nil → g e ∈ A (2 ^ (K + 1 + esize e))) ∧
        (¬ Halts e .nil → g e ∈ B₁ (2 ^ (K + 1 + esize e))) := by sorry
