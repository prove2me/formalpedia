-- Prove2me | Theorems.Thm_GaussOptCVQKD_eq_4_gaussian_extremality
-- name    : GaussOptCVQKD.eq_4_gaussian_extremality
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:00:06.853859+00:00
-- url     : https://prove2.me/theorems/4391ead0-0e65-460e-a796-25b6b2f26c1e
-- title:
--   (4) — extremality of Gaussian states (Wolf–Giedke–Cirac): $f(\rho_{AB})\ge f(\rho^G_{AB})$ for centered states
-- statement:
--   Let $f$ be a real functional of bipartite bosonic states (of every finite mode set, each mode owned by Alice or Bob), and fix a domain: all densities, or an energy sublevel $\{\langle\hat n\rangle\le e\cdot|I|\}$ with $e\ge0$. Suppose that, relative to the domain,
--
--   1. $f$ is lower semicontinuous in trace norm;
--   2. $f$ is invariant under the local Gaussification unitaries, $f(U_G^\dagger\otimes U_G^\dagger\,\rho^{\otimes N}\,U_G\otimes U_G)=f(\rho^{\otimes N})$ for $N=2^m$, and under owner-preserving relabellings of the modes;
--   3. $f$ is strongly super-additive on two copies of a system, $f(\rho_{A_1B_1})+f(\rho_{A_2B_2})\le f(\rho_{A_{1,2}B_{1,2}})$, with equality on product states.
--
--   Then for every density $\rho_{AB}$ in the domain with zero first moments and covariance matrix $\gamma_{AB}$, a Gaussian state $\rho^G_{AB}$ with zero first moments and covariance $\gamma_{AB}$ exists, and every such Gaussian state lies in the domain and satisfies
--   $$
--   f(\rho_{AB})\ge f(\rho^G_{AB}).
--   $$
--
--   This is the theorem the paper applies to $f=K_\beta$; properties i)–iii) of p.3 supply the three hypotheses.
--
--   **Formalization Note** Hypothesis 1 is Support50.P14 `TraceLowerSemicontinuous`; hypotheses 2 and 3 are `GaussificationInvariant` and `CopySuperadditive` of this mission, built from the published Gaussification objects of Support50.P14. Each is implied by the paper's hypothesis, so the theorem contains the printed statement for centered states.
--
--   Differences from the source:
--
--   - generalization: hypothesis 1: continuity in trace norm on all states → lower semicontinuity in trace norm relative to a domain: all densities, or an energy sublevel; reason: continuity implies lower semicontinuity, and the domain 'all densities' is the printed one; the sublevel form is what K satisfies (property i) holds only on sublevels)
--   - generalization: hypotheses 2 and 3 on all states, conclusion f(ρAB) ≥ f(ρ^G_AB) → hypotheses 2 and 3 required only where the states involved lie in the domain (all densities, or an energy sublevel), and the conclusion also asserts that every such ρ^G lies in the domain; reason: with the domain 'all densities' these are the printed hypotheses, so the theorem assumes no more than the paper; ρ^G has the same second moments as ρ, hence the same mean photon number
--   - generalization: hypothesis 3: strong super-additivity for every N → its N = 2 instance (two copies of a system), with equality on products; reason: the N-fold hypothesis implies the two-copy one, so the theorem assumes less
--   - encoding: hypothesis 2: f(U_G† ⊗ U_G† ρ^{⊗N} U_G ⊗ U_G) = f(ρ^{⊗N}) → the same for N = 2^m with the published Sylvester–Hadamard copy mixer at every mode, plus invariance under owner-preserving relabelling; reason: the Gaussification unitary of [15] acts on 2^m copies; the relabelling clause encodes that the paper's f is a function of the bipartite state and does not see mode labels
--   - reading: 'for every bipartite state ρAB with covariance matrix γAB … ρ^G_AB is the Gaussian state with the same γAB' → for every density in the domain with zero first moments and finite second moments (CompleteMoments ρ 0 γ): existence of a centered Gaussian state with covariance γ, and the inequality for every such Gaussian state; reason: the paper sketches (4) 'for bipartite states ρAB that have zero first-order moments' (p.2); the Gaussian state with given moments is unique
--   - generalization: one mode per party ((6)), or N modes per party ((7)) → every finite mode set I with every owner map I → {Alice, Bob}; reason: N = 1 or N modes on each side is the special case of an owner map with one or N modes per party
--   - encoding: covariance matrix of the quadratures → Support50.P14 conventions: vacuum covariance I, x = (a + a†)/√2, CompleteMoments / GaussianAt; reason: Lean convention; same instances
-- source:
--   García-Patrón, Cerf, Unconditional optimality of Gaussian attacks against continuous-variable QKD, arXiv:quant-ph/0608032v1, 'Extremality of Gaussian states', (4), p.2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_GaussOptCVQKD_ExtremalityHypotheses

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Support50.P14 (OscillatorCovariance CompleteMoments GaussianAt InDomain MultipartiteOscillatorFunctional TraceLowerSemicontinuous)

namespace GaussOptCVQKD

/-- **Extremality of Gaussian states, (4)** (Wolf–Giedke–Cirac, ref. [15]), García-Patrón, Cerf,
arXiv:quant-ph/0608032v1, "Extremality of Gaussian states", p.2: "Let us sketch it here for
bipartite states ρAB that have zero first-order moments. Let f be a function satisfying the
properties 1. continuity in trace norm … 2. invariance under local “Gaussification” unitaries …
3. strong super-additivity … Then, for every bipartite state ρAB with covariance matrix γAB, we
have that f(ρAB) ≥ f(ρ^G_AB) (4) where ρ^G_AB is the Gaussian state with the same γAB."

Let `cap` be a domain (`none`: all densities; `some e`, `e ≥ 0`: mean photon number at most `e`
per mode) and `f` a functional of bipartite oscillator states (every finite mode set, every owner
map) that, relative to `cap`, is
1. trace-norm lower semicontinuous (Support50.P14 `TraceLowerSemicontinuous`),
2. invariant under the local Gaussification unitaries `U_G ⊗ U_G` on tensor powers, and under
   owner-preserving relabellings (`GaussificationInvariant`),
3. strongly super-additive on two copies of a system, with equality on product states
   (`CopySuperadditive`).
Then for every density `ρ` in the domain with zero first moments and covariance `γ`, a Gaussian
state with zero first moments and covariance `γ` exists, and every such Gaussian state `ρ^G` lies
in the domain and satisfies `f(ρ^G) ≤ f(ρ)`.

**Formalization Note** Each hypothesis is implied by the printed one (continuity implies lower
semicontinuity; the `N`-fold super-additivity implies its `N = 2` instance; `cap = none` is the
printed domain), so the theorem contains the printed statement for centered states. -/
theorem eq_4_gaussian_extremality (cap : Option ℝ) (hcap : ∀ e, cap = some e → 0 ≤ e)
    (f : MultipartiteOscillatorFunctional 2) (hlsc : TraceLowerSemicontinuous cap f)
    (hinv : GaussificationInvariant cap f) (hssa : CopySuperadditive cap f)
    {I : Type} [Fintype I] (owner : I → Fin 2) (ρ : State (Occupation I))
    (hdom : InDomain cap ρ.coefficients) (γ : OscillatorCovariance I)
    (hmom : CompleteMoments ρ.coefficients 0 γ) :
    (∃ ρG : State (Occupation I), GaussianAt ρG.coefficients 0 γ) ∧
    ∀ ρG : State (Occupation I), GaussianAt ρG.coefficients 0 γ →
      InDomain cap ρG.coefficients ∧ f I owner ρG.coefficients ≤ f I owner ρ.coefficients := by sorry

end GaussOptCVQKD
