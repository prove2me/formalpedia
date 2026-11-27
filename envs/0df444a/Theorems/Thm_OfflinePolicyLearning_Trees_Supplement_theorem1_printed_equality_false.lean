-- Prove2me | Theorems.Thm_OfflinePolicyLearning_Trees_Supplement_theorem1_printed_equality_false
-- name    : OfflinePolicyLearning.Trees.Supplement.theorem1_printed_equality_false
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T08:12:49.207957+00:00
-- url     : https://prove2.me/theorems/a07ce605-846b-48d1-896d-cab4a5df25fd
-- title:
--   Theorem 1, p. 16 (corrected: the printed equality ℛₙ(Πᴰ) = 27.2√2(κ(Π)+8)√(V*/n) + o(1/√n) is false — counterexample)
-- statement:
--   Theorem 1 of the paper asserts: if $(X_1,\Gamma_1),\dots,(X_n,\Gamma_n)$ are iid with bounded support and Assumption 3 holds, then
--   $$\mathcal R_n(\Pi^D)=27.2\sqrt2\,\big(\kappa(\Pi)+8\big)\sqrt{\frac{V^*}{n}}+o\Big(\frac1{\sqrt n}\Big).$$
--   Here $\mathcal R_n(\Pi^D)$ is the Rademacher complexity of the policy-difference class, $V^*=\sup_{\pi_a,\pi_b\in\Pi}\mathbf E[\langle\Gamma,\pi_a(X)-\pi_b(X)\rangle^2]$, $\kappa(\Pi)=\int_0^1\sqrt{\log N_H(\varepsilon^2,\Pi)}\,d\varepsilon$ is the Hamming entropy integral, and Assumption 3 asks for constants $C,D>0$ and $0<\omega<1/2$ with $N_H(\varepsilon,\Pi)\le C\exp(D\varepsilon^{-\omega})$ for $0<\varepsilon<1$.
--
--   The statement is: **this equality is false.** There is a feature space, a law $P$ of bounded feature–score pairs and a nonempty finite class of measurable policies satisfying Assumption 3 for which
--   $$\sqrt n\Big(\mathcal R_n(\Pi^D)-27.2\sqrt2\,(\kappa(\Pi)+8)\sqrt{V^*/n}\Big)\not\to0 .$$
--   For instance: a one-point feature space, $d=2$, the two constant policies, and the deterministic score $\Gamma=(1,0)$. Then $V^*=1$ and $\kappa(\Pi)=\sqrt{\log2}$, while $\mathcal R_n(\Pi^D)=\mathbf E\big|\frac1n\sum_i Z_i\big|\le 1/\sqrt n$; the printed equality would force $\sqrt n\,\mathcal R_n(\Pi^D)\to27.2\sqrt2(\sqrt{\log2}+8)>300$.
--
--   The paper's own derivation, (12) on p. 19 and Appendix C (45)–(47), only yields an upper bound, so the printed "=" is a misprint for "≤". The upper-bound form is not posed here: its proof uses Lemma 1(2), whose argument picks one cover for all point multisets although Definition 4 only provides covers depending on the points, and its validity with these constants is not settled.
--
--   **Formalization Note** The negated claim quantifies over feature types in `Type`, nonempty finite classes of measurable policies, laws with an almost sure bound on the score coordinates, and Assumption 3 in the form "the covering number is finite and at most $C\exp(D\varepsilon^{-\omega})$". Restricting the universally quantified claim to finite measurable classes only makes its negation stronger: a counterexample there is a counterexample to the printed theorem. $o(1/\sqrt n)$ is read as a deterministic sequence $r_n$ with $\sqrt n\,r_n\to0$. $\kappa(\Pi)$ is the extended real entropy integral of the published Hamming layer, converted to a real number; under Assumption 3 it is finite.
--
--   Differences from the source:
--   - correction: ℛₙ(Πᴰ) = 27.2√2(κ(Π)+8)√(V*/n) + o(1/√n) for every such law and class → the negation of that claim (a counterexample exists); reason: with one feature point, two constant policies and Γ = (1,0), √n ℛₙ(Πᴰ) ≤ 1 while the printed right side forces the limit 27.2√2(√log 2 + 8) > 300
--   - encoding: Πᴰ quantified over all classes satisfying the hypotheses → the negated claim is restricted to nonempty finite classes of measurable policies; reason: a restriction of the universally quantified claim strengthens its negation and keeps the Bochner integral honest
-- source:
--   Zhou, Athey & Wager, Offline Multi-Action Policy Learning, arXiv:1810.04778v2, p. 16, Theorem 1 (6); p. 19, (12); App. C, p. 59, (45)–(47); p. 14, Assumption 3; p. 15, Definition 5

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Hamming
import Definitions.Def_OfflinePolicyLearning_Trees_Supplement_Setting

open MeasureTheory Filter Topology

namespace OfflinePolicyLearning.Trees.Supplement

/-- Theorem 1 (6), p. 16, as printed — `ℛₙ(Πᴰ) = 27.2√2(κ(Π) + 8)√(V*/n) + o(1/√n)` for iid
bounded feature–score pairs under Assumption 3 — is false. Its negation is stated already for
nonempty finite classes of measurable policies (a special case of the printed hypotheses). -/
theorem theorem1_printed_equality_false :
    ¬ ∀ (X : Type) [MeasurableSpace X] (d : ℕ) (P : Measure (X × (Fin d → ℝ)))
        [IsProbabilityMeasure P] (Pol : Set (X → Fin d)),
        Pol.Nonempty → Pol.Finite → (∀ π ∈ Pol, Measurable π) →
        (∃ B : ℝ, ∀ᵐ z ∂P, ∀ j, |z.2 j| ≤ B) →
        (∃ C D ω : ℝ, 0 < C ∧ 0 < D ∧ 0 < ω ∧ ω < 1 / 2 ∧
          ∀ ε : ℝ, 0 < ε → ε < 1 →
            OfflinePolicyLearning.Regret.hammingCoverNum ε Pol ≠ ⊤ ∧
            ((OfflinePolicyLearning.Regret.hammingCoverNum ε Pol).toNat : ℝ) ≤
              C * Real.exp (D * (1 / ε) ^ ω)) →
        Tendsto (fun n : ℕ => Real.sqrt n * (policyDiffRademacher P n Pol -
            27.2 * Real.sqrt 2 * ((OfflinePolicyLearning.Regret.entropyIntegral Pol).toReal + 8) *
              Real.sqrt (scoreVstar P Pol / n)))
          atTop (𝓝 0) := by sorry

end OfflinePolicyLearning.Trees.Supplement
