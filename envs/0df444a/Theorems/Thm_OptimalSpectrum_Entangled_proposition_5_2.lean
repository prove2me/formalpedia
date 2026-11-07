-- Prove2me | Theorems.Thm_OptimalSpectrum_Entangled_proposition_5_2
-- name    : OptimalSpectrum.Entangled.proposition_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:20:58.785636+00:00
-- url     : https://prove2.me/theorems/64d07dd0-9e2a-4d29-8031-0db1852efac1
-- title:
--   Proposition 5.2 — entangled bucketing at cost $O(d/(B\eta^2))$
-- statement:
--   There is a universal constant $C>0$ such that for every dimension $d$ and every $0<B<1$, $0<\eta<1$, there are $N\le C\,d/(B\eta^2)$ and a POVM on $(\mathbb C^d)^{\otimes N}$ with outcomes $(\Pi,\widehat\alpha_{\mathrm{Large}})$, an orthogonal projector and a sorted nonnegative list of length $\mathrm{rank}\,\Pi$, such that for every density matrix $\rho$ on $\mathbb C^d$, with probability at least $0.99$, the outcome satisfies
--
--   1. $d_{\mathrm{TV}}(\alpha_{\mathrm{Large}},\widehat\alpha_{\mathrm{Large}})\le\eta$, where $\alpha_{\mathrm{Large}}=\mathrm{spec}(\Pi\rho\Pi|_{\mathrm{ran}\,\Pi})$;
--   2. $0\preceq\overline\Pi\rho\overline\Pi\preceq1.1B\,I_d$;
--   3. $d_{\mathrm{TV}}\big(\mathrm{spec}(\rho),\mathrm{spec}(\Pi\rho\Pi+\overline\Pi\rho\overline\Pi)\big)\le\eta$.
--
--   This is the first stage of the paper's algorithm: it learns the eigenvalues above the threshold $B$ and isolates a small-bucket state $\sigma=\overline\Pi\rho\overline\Pi$ with spectrum in $[0,1.1B]$. The paper imports it from Pelecanos–Spilecki–Tang–Wright and does not prove it.
--
--   Differences from the source:
--   - encoding: α̂_Large a list of length rank Π, α_Large = spec(ΠρΠ|_ran Π) → zero-padded vector of length d compared with the full sorted spectrum spec(ΠρΠ); reason: the eigenvalues of ΠρΠ beyond rank Π are zero, so both vectors are the lists followed by zeros and the distance is unchanged
--   - encoding: probability at least 0.99 → inner probability: a measurable subset of the success event has Born probability ≥ 0.99; reason: equals the probability when the event is measurable and is never weaker
--   - encoding: "implemented using entangled measurements", cost O(d/(Bη²)) → ∃ C > 0 before d, B, η; ∃ N ≤ C d/(Bη²) and a POVM on (ℂ^d)^⊗N chosen before ρ; reason: Definition 4.1 entangled model; O(·) is uniform in d, B, η
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Proposition 5.2, p. 13 (PDF p. 15)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
import Definitions.Def_OptimalSpectrum_Entangled_BucketOutcome
import Definitions.Def_OptimalSpectrum_Entangled_bucketingSuccess
import Definitions.Def_OptimalSpectrum_Entangled_copiesLaw

open MeasureTheory

namespace OptimalSpectrum.Entangled

/-- **Proposition 5.2 (Entangled bucketing algorithm).**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, Proposition 5.2, printed p. 13 (PDF p. 15): "For every 0 < B < 1 and 0 < η < 1, there is a
bucketing algorithm at (B, η) of cost N = O(d/(Bη²)), implemented using entangled measurements."

With Definition 5.1 (printed p. 12): there is an absolute `C > 0` such that for every `d`, every
`B, η ∈ (0, 1)`, there are `N ≤ C d/(Bη²)` and a POVM on `(ℂ^d)^{⊗N}` whose outcomes are pairs
(orthogonal projector `Π`, sorted nonnegative list of length `rank Π`), such that for every density
matrix `ρ` the outcome satisfies the three bounds (i)–(iii) of Definition 5.1 with probability at
least `0.99`.

**Formalization Note.** The paper imports this from [PSTW26, Definition 5.2, Lemma 5.3,
Lemma 5.4(2)] and does not prove it. The probability is stated as an inner probability (a measurable
subset of the success event of probability `≥ 0.99`); it equals the probability of the event when the
event is measurable and is never weaker. -/
theorem proposition_5_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, ∀ B η : ℝ, 0 < B → B < 1 → 0 < η → η < 1 →
      ∃ N : ℕ, (N : ℝ) ≤ C * d / (B * η ^ 2) ∧
        ∃ E : QAlgorithms.Measurements.OperatorPOVM (Fin N → Fin d) (BucketOutcome d),
          ∀ (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ),
            ∃ S : Set (BucketOutcome d), MeasurableSet S ∧ S ⊆ {o | bucketingSuccess B η ρ o} ∧
              ENNReal.ofReal (99 / 100) ≤ copiesLaw E ρ hρ S := by sorry

end OptimalSpectrum.Entangled
