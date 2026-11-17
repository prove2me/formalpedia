-- Prove2me | Theorems.Thm_GSRandomOrder_Supplement_theorem_4_5
-- name    : GSRandomOrder.Supplement.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:12:04.743391+00:00
-- url     : https://prove2.me/theorems/2ee1dd15-aaf1-4735-a45a-c7e5cfabf8c0
-- title:
--   Theorem 4.5 — conditional admission implies welfare $c_n(s)\,\mathrm{OPT}$
-- statement:
--   Let $v_1,\dots,v_m$ be GS valuations on $N=\{1,\dots,n\}$ and let $s\in\{1,\dots,n-1\}$. For every $S\subseteq N$ fix an optimal allocation $X^S=(X^S_1,\dots,X^S_m)$ of $S$, and let bidder $i$'s proposal map be $P_i(S)=X^S_i$. Suppose every bidder $i$ has an admission module for $v_i$ and $P_i$ with cutoff $s$ that has **conditional admission** (Definition 4.4). Run the modules side by side on the uniformly random arrivals, each with its own coins, and give each item to the bidder whose module accepts it, discarding it if there is none. Then
--
--   1. this is an online algorithm for welfare: at most one module accepts each item, so the bundles $A_i$ (the accepted sets of the modules) are pairwise disjoint;
--   2. its expected welfare satisfies
--   $$
--   \mathbb E\sum_{i=1}^m v_i(A_i)\ \ge\ c_n(s)\,\mathrm{OPT},\qquad c_n(s)=\frac sn\sum_{j=s}^{n-1}\frac1j,
--   $$
--   where $\mathrm{OPT}=W(N)$.
--
--   The theorem reduces welfare with many GS bidders to a property of a single bidder; with the best cutoff it gives $1/e$ (Lemma D.1), and it is the step that turns the linear-matroid algorithm of Abdi et al. into Theorem E.1.
--
--   **Formalization Note** Modules are behavioural rules (see `AdmissionModule`); the side-by-side run gives the order $\sigma$ mass $1/n!$ and the decision vectors of the modules the product of their decision probabilities. Disjointness is stated on every outcome of positive probability. $v_i(A_i)$ is read as a real number.
--
--   Differences from the source:
--   - generalization: X^S chosen from the labels and the values of subsets of S alone → any map S ↦ X S with X S an optimal allocation of S; reason: the conclusion for every optimal-allocation map contains the case of maps computed locally
--   - generalization: admission modules: online algorithms that observe the arrivals, may query v and P on arrived sets, and use their own coins → every behavioural rule prob(g_1..g_k; d_1..d_{k−1}) ∈ [0,1] that rejects for k ≤ s and for g_k ∉ P(S_k), with arbitrary dependence on v and P; reason: every module of the paper has such a rule with the same joint law of order and decisions (Kuhn), and the hypotheses and conclusion depend only on that law; a larger class of modules makes the statement stronger
--   - reading: run the modules side by side → the modules use independent coins: joint mass (1/n!) Π_i weight_i(σ, D_i); reason: each module is an algorithm with its own coins; the statement fixes no coupling
--   - encoding: conditional probabilities in (15); A ∈ dom v almost surely → (15) multiplied out by P[S_k = S, g_k = g]; "on every outcome of positive mass"; reason: the conditioning event has positive probability; the sample space is finite
--   - encoding: this is an online algorithm for welfare → on every outcome of positive mass at most one module accepts each arrival, so the bundles A_i (module i's accepted sets) are pairwise disjoint; reason: online-ness of the combined rule is structural (each module sees only arrivals and its own decisions)
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), §4.3, p.16, Theorem 4.5; Definition 4.4, pp.15–16; prefix proposals, p.15

import Mathlib
import Definitions.Def_GSRandomOrder_IsGSValuation
import Definitions.Def_GSRandomOrder_Supplement_welfare
import Definitions.Def_GSRandomOrder_Supplement_IsOptimalAllocation
import Definitions.Def_GSRandomOrder_Supplement_cn
import Definitions.Def_GSRandomOrder_Supplement_AdmissionModule
import Definitions.Def_GSRandomOrder_Supplement_HasConditionalAdmission

set_option autoImplicit false

namespace GSRandomOrder.Supplement

/-- **Theorem 4.5 (Conditional admission implies welfare)** (R. Paes Leme, M. Pál, N. Patel,
*Gross Substitutes Welfare in Random Order*, STOC 2027 submission, manuscript sha256 69787f50…,
§4.3, p.16). Let `v_1, …, v_m` be GS valuations and `s ∈ {1, …, n − 1}`, and suppose that every
bidder `i` has an admission module for `v_i` and `P_i(S) = X^S_i` with conditional admission. Run
the modules side by side on the arrivals, and give each item to the bidder whose module accepts
it, discarding it if there is none. This is an online algorithm for welfare, and
`E Σ_{i=1}^m v_i(A_i) ≥ c_n(s) OPT`.

**Formalization Note.**
* `X S` is an optimal allocation of `S` for every `S` (the prefix optima `X^S`, fixed in
  advance); the paper's extra requirement that `X^S` be computed from the labels and values on
  subsets of `S` is dropped, which only strengthens the statement.
* The modules are arbitrary behavioural rules (`AdmissionModule`), each for its own proposal map
  `S ↦ X S i`, with conditional admission under its own law. Side by side, the modules use
  independent coins: decisions `D i` of module `i` have joint mass
  `(1/n!) Π_i (M i).weight σ (D i)` with the order `σ`.
* "This is an online algorithm for welfare": on every outcome of positive mass, at most one
  module accepts each arrival, so the bundles `A_i = acceptedSet σ (D i)` (module `i`'s accepted
  set) are pairwise disjoint; online-ness of the combined rule is structural.
* `OPT = W(N)` is `welfare v univ`; `v_i(A_i)` is read with `unbotD 0` (each `A_i ∈ dom v_i`
  almost surely by condition (ii)). -/
theorem theorem_4_5 {n m : ℕ} (v : Fin m → Finset (Fin n) → WithBot ℝ)
    (hv : ∀ i, IsGSValuation (v i)) (s : ℕ) (hs : 1 ≤ s) (hsn : s < n)
    (X : Finset (Fin n) → Fin m → Finset (Fin n)) (hX : ∀ S, IsOptimalAllocation v S (X S))
    (M : (i : Fin m) → AdmissionModule n (fun S => X S i) s)
    (hM : ∀ i, HasConditionalAdmission (v i) (M i)) :
    (∀ (σ : Fin n ≃ Fin n) (D : Fin m → Fin n → Bool), (∏ i, (M i).weight σ (D i)) ≠ 0 →
      ∀ (j : Fin n) (i i' : Fin m), D i j = true → D i' j = true → i = i') ∧
    cn n s * welfare v Finset.univ ≤
      ∑ σ : Fin n ≃ Fin n, ∑ D : Fin m → Fin n → Bool,
        (1 / (n.factorial : ℝ)) * (∏ i, (M i).weight σ (D i)) *
          ∑ i, (v i (acceptedSet σ (D i))).unbotD 0 := by sorry

end GSRandomOrder.Supplement
