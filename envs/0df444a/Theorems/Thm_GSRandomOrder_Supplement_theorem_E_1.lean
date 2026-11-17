-- Prove2me | Theorems.Thm_GSRandomOrder_Supplement_theorem_E_1
-- name    : GSRandomOrder.Supplement.theorem_E_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:12:46.047808+00:00
-- url     : https://prove2.me/theorems/ab1225e3-aa42-44f1-bafd-60e66191feb5
-- title:
--   Theorem E.1 — matroid welfare $c_n(s)\,\mathrm{OPT}$ for linear matroid bidders (represented and oracle models)
-- statement:
--   Let bidder $i$ have a matroid $M_i$ on $N=\{1,\dots,n\}$ and real weights $w_{ig}$, possibly negative and different across bidders, with the valuation (31): $v_i(S)=\sum_{g\in S}w_{ig}$ if $S$ is independent in $M_i$ and $v_i(S)=-\infty$ otherwise. Let $n\ge2$ and let the items arrive in uniformly random order. Suppose that either
--
--   1. **(a)** each $M_i$ is represented over a finite field $\mathbb F_i$ by vectors $u_{ig}$, in the represented model (when $g$ arrives the algorithm learns $u_{ig}$ for every $i$, and it may query values of sets of arrived items); or
--   2. **(b)** each $M_i$ is binary or ternary, a field $\mathbb F_i\in\{\mathbb F_2,\mathbb F_3\}$ over which $M_i$ is represented is known to the algorithm, and the algorithm is in the oracle model (value queries on sets of arrived items only).
--
--   Then for every cutoff $s\in\{1,\dots,n-1\}$ there is an online algorithm that keeps every bundle independent at every time and satisfies
--   $$
--   \mathbb E\sum_{i=1}^m v_i(A_i)\ \ge\ c_n(s)\,\mathrm{OPT},\qquad c_n(s)=\frac sn\sum_{j=s}^{n-1}\frac1j,
--   $$
--   where $\mathrm{OPT}=W(N)$. For the cutoff of Lemma D.1 the right side is at least $\mathrm{OPT}/e$.
--
--   With the best cutoff this is Theorem C: the optimal $1/e$ for welfare with weighted linear-matroid bidders. The fields may differ across bidders.
--
--   **Formalization Note** The algorithm is chosen after $n$, $m$, the fields (and in (a) the dimensions) and the cutoff, and before the instance (vectors and weights); its input contains only the observation of the arrived prefix and its own earlier actions. Independence of bundles is stated on every outcome of positive probability after every number of arrivals. The last sentence is stated as the existence of a cutoff with $c_n(s)\ge1/e$.
--
--   Differences from the source:
--   - encoding: M_i represented over F_i (a), binary or ternary with a known field F_i ∈ {F2, F3} (b) → M_i given by vectors u_i : Fin n → (Fin d_i → F_i) with independence LinearIndepOn; in (b) F_i = ZMod (p i) with p i ∈ {2, 3}, any dimension d_i and any vectors quantified after the algorithm; reason: a matroid is representable over a field iff it is given by such vectors, and (31) depends on the matroid only
--   - encoding: there is an online algorithm (represented model: labels, values of arrived sets, vectors of arrived items; oracle model: value queries only) → ∃ behavioural rule whose input is the observation after each arrival (labels, values v_i(T) for T ⊆ S_k, and in (a) the vectors u_ig of arrived g) and its own earlier actions; the dimensions d_i in (a) are fixed before the rule; reason: behavioural rules have exactly the joint laws of randomized online algorithms with perfect recall (Kuhn); the first arriving vector reveals d_i, and no action is taken before it
--   - encoding: keeps every bundle independent at every time → on every outcome of positive mass, every bundle after every number t of arrivals is linearly independent; reason: the sample space is finite
--   - encoding: For the cutoff of Lemma D.1 the right side is at least OPT/e → ∃ s ∈ {1, …, n − 1} with 1/e ≤ c_n(s); reason: OPT ≥ 0, so c_n(s) OPT ≥ OPT/e for every instance iff c_n(s) ≥ 1/e (OPT > 0 occurs); this s is the cutoff of Lemma D.1
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), App. E, p.32, Theorem E.1 (= Theorem C, p.4); eq. (31) and the two models, pp.31–32

import Mathlib
import Definitions.Def_GSRandomOrder_Supplement_welfare
import Definitions.Def_GSRandomOrder_Supplement_cn
import Definitions.Def_GSRandomOrder_Supplement_prefixSet
import Definitions.Def_GSRandomOrder_Supplement_linMatroidVal
import Definitions.Def_GSRandomOrder_Supplement_OnlineWelfareRule

set_option autoImplicit false

namespace GSRandomOrder.Supplement

/-- **Theorem E.1 (Matroid welfare)** (R. Paes Leme, M. Pál, N. Patel, *Gross Substitutes Welfare
in Random Order*, STOC 2027 submission, manuscript sha256 69787f50…, App. E, p.32; Theorem C,
p.4, is the case of the best cutoff). Let the bidders have the valuations (31), let `n ≥ 2`, and
let the items arrive in uniformly random order. Suppose that either
(a) each `M_i` is represented over a finite field `F_i`, in the represented model; or
(b) each `M_i` is binary or ternary, a field `F_i ∈ {F_2, F_3}` over which `M_i` is represented
    is known to the algorithm, and the algorithm is in the oracle model.
Then for every cutoff `s ∈ {1, …, n − 1}` there is an online algorithm that keeps every bundle
independent at every time and satisfies `E Σ_{i=1}^m v_i(A_i) ≥ c_n(s) OPT`,
`c_n(s) = (s/n) Σ_{j=s}^{n−1} 1/j`. For the cutoff of Lemma D.1 the right side is at least
`OPT/e`.

**Formalization Note.**
* The order is a uniform bijection `σ` (mass `1/n!`); the algorithm is a behavioural rule
  (`OnlineWelfareRule`) whose input is the observation after the `k`-th arrival: the labels
  `g_1, …, g_k`, the values `v_i(T)` for `T ⊆ S_k` (`valueObs`), and in (a) the vectors `u_{ig}`
  of the arrived items (`vectorObs`). It never sees the instance otherwise.
* Quantifier order. (a): `n, m`, the finite fields `F_i` and dimensions `d_i`, the cutoff `s`,
  then the algorithm, then every instance (vectors `u_i`, real weights `w_i` of any sign).
  (b): `n, m`, the known fields `ZMod (p i)` with `p i ∈ {2, 3}`, `s`, then the algorithm, then
  every binary/ternary instance: any dimension `d_i`, vectors over `ZMod (p i)` and weights; the
  algorithm sees no vectors. A matroid is represented over a field iff it is given by such
  vectors, and (31) depends on the matroid only.
* "Keeps every bundle independent at every time": on every outcome of positive mass, every
  bundle after every number `t` of arrivals is independent in `M_i`. `OPT = W(N)`; `v_i(A_i)` is
  read with `unbotD 0`, exact by independence.
* The last sentence is the third conjunct: some cutoff `s ∈ {1, …, n − 1}` has
  `c_n(s) ≥ 1/e`, so `c_n(s) OPT ≥ OPT/e` (as `OPT ≥ 0`). -/
theorem theorem_E_1 {n m : ℕ} (hn : 2 ≤ n) :
    (∀ (F : Fin m → Type) [∀ i, Field (F i)] [∀ i, Fintype (F i)] (d : Fin m → ℕ) (s : ℕ),
      1 ≤ s → s < n →
      ∃ R : OnlineWelfareRule
          (List (Fin n) × (Fin m → Finset (Fin n) → WithBot ℝ) ×
            ((i : Fin m) → Fin n → Option (Fin (d i) → F i))) m,
        ∀ (u : (i : Fin m) → Fin n → Fin (d i) → F i) (w : Fin m → Fin n → ℝ),
          (∀ (σ : Fin n ≃ Fin n) (D : Fin n → Option (Fin m)),
            R.weight (fun t => (prefixList σ t,
                valueObs (fun i => linMatroidVal (u i) (w i)) (prefixSet σ t),
                vectorObs u (prefixSet σ t))) D ≠ 0 →
              ∀ (i : Fin m) (t : ℕ), LinearIndepOn (F i) (u i) (bundleAt σ D i t : Set (Fin n))) ∧
          cn n s * welfare (fun i => linMatroidVal (u i) (w i)) Finset.univ ≤
            ∑ σ : Fin n ≃ Fin n, ∑ D : Fin n → Option (Fin m),
              (1 / (n.factorial : ℝ)) *
                R.weight (fun t => (prefixList σ t,
                  valueObs (fun i => linMatroidVal (u i) (w i)) (prefixSet σ t),
                  vectorObs u (prefixSet σ t))) D *
                ∑ i, (linMatroidVal (u i) (w i) (bundleAt σ D i n)).unbotD 0) ∧
    (∀ (p : Fin m → ℕ), (∀ i, p i = 2 ∨ p i = 3) → ∀ s : ℕ, 1 ≤ s → s < n →
      ∃ R : OnlineWelfareRule (List (Fin n) × (Fin m → Finset (Fin n) → WithBot ℝ)) m,
        ∀ (d : Fin m → ℕ) (u : (i : Fin m) → Fin n → Fin (d i) → ZMod (p i))
          (w : Fin m → Fin n → ℝ),
          (∀ (σ : Fin n ≃ Fin n) (D : Fin n → Option (Fin m)),
            R.weight (fun t => (prefixList σ t,
                valueObs (fun i => linMatroidVal (u i) (w i)) (prefixSet σ t))) D ≠ 0 →
              ∀ (i : Fin m) (t : ℕ),
                LinearIndepOn (ZMod (p i)) (u i) (bundleAt σ D i t : Set (Fin n))) ∧
          cn n s * welfare (fun i => linMatroidVal (u i) (w i)) Finset.univ ≤
            ∑ σ : Fin n ≃ Fin n, ∑ D : Fin n → Option (Fin m),
              (1 / (n.factorial : ℝ)) *
                R.weight (fun t => (prefixList σ t,
                  valueObs (fun i => linMatroidVal (u i) (w i)) (prefixSet σ t))) D *
                ∑ i, (linMatroidVal (u i) (w i) (bundleAt σ D i n)).unbotD 0) ∧
    (∃ s : ℕ, 1 ≤ s ∧ s < n ∧ Real.exp (-1) ≤ cn n s) := by sorry

end GSRandomOrder.Supplement
