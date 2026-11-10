-- Prove2me | Theorems.Thm_MinSumRadiiPTAS_Main_claim_6_5
-- name    : MinSumRadiiPTAS.Main.claim_6_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:06:50.778891+00:00
-- url     : https://prove2.me/theorems/444cd8fc-c90d-4e97-b562-f2261e1659ed
-- title:
--   Claim 6.5 — certified balls: (a) $O_{3R} \subseteq \mathcal C_R$; (b) covers of $C \cap P''$ by radius-$\le 3R$ balls cost $\ge (r_C+\lambda)/3$
-- statement:
--   **Claim 6.5** (p. 26). In Case II on a normalised instance, after any terminated run of the preprocessing (leaving $P''$) and for any optimal $O_{3R}$ for $P''$:
--
--   (a) $O_{3R} \subseteq \mathcal C_R$, i.e. every ball of $O_{3R}$ is certified;
--
--   (b) for every $C \in \mathcal C_R$ and every finite set $D$ of balls with radii in $[0, 3R]$ that covers $C \cap P''$,
--   $$\mathrm{cost}_\lambda(D) \ge \frac{r_C + \lambda}{3}.$$
--
--   Differences from the source:
--   - encoding: point set P with |P| = n, a metric d on P → points Fin n (0-based), d : Fin n → Fin n → ℝ with the published MinSumClust.IsMetric (d(p,p)=0, d ≥ 0, symmetry, triangle inequality, d(p,q) > 0 for p ≠ q); reason: same instances
--   - encoding: balls Ball(c, r) with r ∈ ℝ≥0 and sets of balls → Ball n = (center : Fin n, radius : ℝ) with point set {p : d(c,p) ≤ r}; arbitrary input/output balls carry 0 ≤ radius explicitly; mathematical sets of balls are Finsets; reason: same objects; a negative radius is not a ball (p. 1)
--   - reading: the lemma's own sentence (context of §6) → explicit hypotheses: StandingInstance d k ε (Lemma 2.1's normalisation: integer distances in [1, ⌈10k/ε⌉], opt ≤ 8k/ε, 1 ≤ k ≤ n), ε ∈ (0, 1/10), λ ∈ [ε/k, 10k/ε] (Theorem 6.1); reason: p. 7 assumes the normalisation for the rest of the paper, p. 6 fixes ε ∈ (0, 1/10), and §6 works under Theorem 6.1's λ; trap 19 (section standing assumptions are binders)
--   - reading: P″ and O_{3R} of §6.2 (Case II, λ < 6R) → P″ := preFinal of any terminated run of the preprocessing (IsPreprocessingRun) from any client set P′, O_{3R} any optimal cover of P″ by balls of 𝔅 of radius ≤ 3R (IsOptCover); reason: the paper's preprocessing picks dense balls in an arbitrary order and O_{3R} is any optimal solution; the statement holds for all of them
--   - generalization: p. 26 assumes R ≤ ⌈10k/ε⌉ without loss before the bounded-radius DP analysis → no upper bound on R beyond the Case II condition λ < 6R; reason: this includes every source instance. Above the maximum distance all minimal balls are allowed and no dense preprocessing ball exists; extra threshold levels have empty nets and only a far child. The algorithm can cap R and use Case I if needed
-- source:
--   Fabrizio Grandoni, Anupam Gupta, Jatin Yadav, A PTAS for the Minimum Sum of Radii Problem, manuscript dated November 3, 2026 (STOC 2027 submission), SHA-256 99b43d49…, §6.2, Claim 6.5, p. 26 (proof pp. 26–27)

import Mathlib
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_MinSumRadiiPTAS_Main_LP
import Definitions.Def_MinSumRadiiPTAS_Main_CaseII

open scoped Classical

namespace MinSumRadiiPTAS.Main

/-- **Claim 6.5** (p. 26): in Case II on a normalised instance, after any terminated run of the
preprocessing (client set `P″`) and for any optimal `O_{3R}` for `P″`:
(a) `O_{3R} ⊆ C_R`;
(b) for every `C ∈ C_R` and every finite set `D` of balls with radii in `[0, 3R]` covering
`C ∩ P″`, `cost_λ(D) ≥ (r_C + λ)/3`. -/
theorem claim_6_5 {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε lam R : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1 / 10) (hI : StandingInstance d k ε) (hlam1 : ε / k ≤ lam)
    (hlam2 : lam ≤ 10 * k / ε) (hcase : lam < 6 * R) (P1 : Finset (Fin n))
    (steps : List (Fin n × ℝ)) (hrun : IsPreprocessingRun d lam ε R P1 steps)
    (O3 : Finset (Ball n))
    (hO3 : IsOptCover d lam (fun B => B.radius ≤ 3 * R) (preFinal d R P1 steps) O3) :
    (∀ B ∈ O3, IsCertifiedR d lam R (preFinal d R P1 steps) B) ∧
      ∀ C : Ball n, IsCertifiedR d lam R (preFinal d R P1 steps) C →
        ∀ D : Finset (Ball n), (∀ B ∈ D, 0 ≤ B.radius ∧ B.radius ≤ 3 * R) →
          Covers d D (C.pts d ∩ preFinal d R P1 steps) →
            (C.radius + lam) / 3 ≤ costL lam D := by sorry

end MinSumRadiiPTAS.Main
