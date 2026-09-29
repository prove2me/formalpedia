-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_smul_eq_zero
-- name    : ModularCurve.ModularPolynomialData.eval_E4_cube_div_discriminant_smul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/eccf1cb1-5baa-5df8-bcbf-cef680be6556
-- title:
--   Modular equation on H: Φ_N(j(σ),j(Nσ))=0
-- statement:
--   Fix a non-zero natural number $N$ and a packet `data` of modular-polynomial data of level $N$, that is, a polynomial $\Phi =$ `data.Φ` in $\mathbb Z[X][Y]$ which is monic in $Y$, whose degree in $Y$ equals `dedekindPsi N` $= \sum_{d \mid N,\ d \text{ squarefree}} N/d$, and which satisfies the formal identity `Φ.eval₂ evalAtJ (jqN N) = 0` in the field of Laurent series over $\mathbb Q$, where `evalAtJ` is the ring homomorphism $\mathbb Z[X] \to \mathbb Q((q))$ evaluating at the formal $q$-expansion `jq` of $j$ and `jqN N` is the corresponding series attached to $N$. Let $\sigma, \sigma'$ be points of the upper half-plane whose coordinates satisfy $\sigma' = N\sigma$ in $\mathbb C$. The conclusion is that the complex polynomial in one variable obtained from $\Phi$ by applying to each coefficient in $\mathbb Z[X]$ the evaluation homomorphism sending $X$ to $E_4(\sigma)^3/\Delta(\sigma)$ and integers to their images in $\mathbb C$, when evaluated at $E_4(\sigma')^3/\Delta(\sigma')$, gives $0$; here $E_4$ is the normalised weight-four Eisenstein series and $\Delta$ the discriminant modular form of level one.
--
--   This is the analytic form of the modular equation: the classical relation $\Phi_N(j(\sigma), j(N\sigma)) = 0$ on the upper half-plane, with $j$ written as $E_4^3/\Delta$ and with $\Phi_N$ taken from any packet of modular-polynomial data specified by its formal $q$-expansion identity. It is used to pass from the formal identity between $q$-expansions to values at points of $\mathfrak H$, and is cited in the corresponding statement for the other points of the $\Gamma_0(N)$-coset, [`ModularCurve.ModularPolynomialData.eval_E4_cube_div_discriminant_coset_eq_zero`](thm.html#ModularCurve.ModularPolynomialData.eval_E4_cube_div_discriminant_coset_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_smul_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PrimCosetReps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane

theorem ModularCurve.ModularPolynomialData.eval_E4_cube_div_discriminant_smul_eq_zero (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) (σ σ' : ℍ) (hσ' : (σ' : ℂ) = (N : ℂ) * σ) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ)
        ((ModularForm.E₄ : ℍ → ℂ) σ ^ 3 / ModularForm.discriminant σ))).eval
      ((ModularForm.E₄ : ℍ → ℂ) σ' ^ 3 / ModularForm.discriminant σ') = 0 := by sorry
