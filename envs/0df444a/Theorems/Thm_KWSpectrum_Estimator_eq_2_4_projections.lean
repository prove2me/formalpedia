-- Prove2me | Theorems.Thm_KWSpectrum_Estimator_eq_2_4_projections
-- name    : KWSpectrum.Estimator.eq_2_4_projections
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:38.515521+00:00
-- url     : https://prove2.me/theorems/29dded7d-8310-48f7-bad4-65bbc7f29fdc
-- title:
--   Eqs. (2)–(4) — the $P_Y$ are complete orthogonal projections commuting with $X^{\otimes N}$ and $S_p$, and $\operatorname{tr}(S_pP_Y) = \dim\mathcal R_Y\,\hat\chi_Y(p)$
-- statement:
--   Let $d, N \in \mathbb N$. For a Young frame $Y$ with $N$ boxes and at most $d$ rows, let $P_Y$ be the projection of $(\mathbb C^d)^{\otimes N}$ onto the summand $\mathcal R_Y\otimes\mathcal S_Y$ of the decomposition
--   $$\mathcal H^{\otimes N} \cong \bigoplus_Y \mathcal R_Y \otimes \mathcal S_Y,\qquad X^{\otimes N} \cong \bigoplus_Y \pi_Y(X)\otimes \mathbb 1,\qquad S_p \cong \bigoplus_Y \mathbb 1\otimes \hat\pi_Y(p),$$
--   where $S_p\,\psi_1\otimes\dots\otimes\psi_N = \psi_{p^{-1}1}\otimes\dots\otimes\psi_{p^{-1}N}$ permutes the tensor factors. Then for all frames $Y \ne Y'$:
--
--   1. $P_Y \ne 0$;
--   2. $P_Y^* = P_Y$ and $P_Y^2 = P_Y$;
--   3. $P_Y P_{Y'} = 0$;
--   4. $\sum_Y P_Y = \mathbb 1$;
--   5. $P_Y$ commutes with $X^{\otimes N}$ for every $d\times d$ complex matrix $X$, and with $S_p$ for every permutation $p$ of $N$ points;
--   6. on the range of $P_Y$ the permutations act as $\mathbb 1\otimes\hat\pi_Y(p)$ on $\mathcal R_Y\otimes\mathcal S_Y$, in trace form: $\operatorname{tr}(S_p P_Y) = \dim(\mathcal R_Y)\,\hat\chi_Y(p)$ for every $p$, where $\hat\chi_Y$ is the character of the Specht representation $\hat\pi_Y$ and $\mathcal R_Y$ is the Schur module.
--
--   These are the properties of the decomposition (2)–(4) that the paper's argument uses: they make $E_N(\Delta)=\sum_{Y/N\in\Delta}P_Y$ a projection-valued measure, hence $K_N$ a probability measure, and they underlie the trace formula (17).
--
--   **Formalization Note** $P_Y$ is the published `isotypicProjector`, defined from the permutation action alone as $\frac{\dim\mathcal S_Y}{N!}\sum_p \chi_Y(p^{-1})S_p$; none of the listed properties is assumed. The commutant theorem cited by the paper ([13]) is not part of the statement.
--
--   Differences from the source:
--   - generalization: commutation with $X^{\otimes N}$ for $X \in GL(d,\mathbb C)$ → for every complex $d\times d$ matrix $X$; reason: $P_Y$ is a combination of the $S_p$, which commute with every $X^{\otimes N}$; the invertible case is included.
--   - reading: "the projection onto the corresponding summand" of the decomposition (2)–(4) → the listed projection, orthogonality, completeness and commutation properties of the isotypic projector, with (4) on the summand in trace form, $\operatorname{tr}(S_pP_Y) = \dim\mathcal R_Y\,\hat\chi_Y(p)$ (the trace form of (3) on the summand is eq. (17)); reason: these are the properties of the summand projections that the argument uses; the decomposition itself rests on the cited commutant theorem [13].
-- source:
--   Keyl & Werner, Estimating the spectrum of a density operator, arXiv:quant-ph/0102027v1, p. 2, eqs. (1)–(4) and the definition of P_Y

import Mathlib
import Definitions.Def_KWSpectrum_Estimator_Model

namespace KWSpectrum.Estimator

open QAlgorithms QAlgorithms.Schur
open scoped Matrix

/-- Keyl–Werner, arXiv:quant-ph/0102027v1, p. 2, eqs. (2)–(4): the projections `P_Y` onto the
summands `R_Y ⊗ S_Y` of `(ℂ^d)^{⊗N}` (the isotypic projections of the permutation action
`p ↦ S_p`) are nonzero orthogonal projections, mutually orthogonal, sum to the identity,
commute with every `X^{⊗N}` and every `S_p`, and on the range of `P_Y` the permutations act as
`1 ⊗ π̂_Y(p)` (eq. (4)): `tr(S_p P_Y) = dim(R_Y) · χ̂_Y(p)`, `χ̂_Y` the Specht character. -/
theorem eq_2_4_projections {d N : ℕ} (Y : Partition d N) :
    isotypicProjector Y ≠ 0 ∧
    (isotypicProjector Y)ᴴ = isotypicProjector Y ∧
    isotypicProjector Y * isotypicProjector Y = isotypicProjector Y ∧
    (∀ Y' : Partition d N, Y' ≠ Y → isotypicProjector Y * isotypicProjector Y' = 0) ∧
    (∑ Y' : Partition d N, isotypicProjector Y') = 1 ∧
    (∀ X : Matrix (Fin d) (Fin d) ℂ, Commute (isotypicProjector Y) (piKron N X)) ∧
    (∀ p : Equiv.Perm (Fin N), Commute (isotypicProjector Y) (tensorPermutation d N p)) ∧
    (∀ p : Equiv.Perm (Fin N), (tensorPermutation d N p * isotypicProjector Y).trace =
      (Module.finrank ℂ (schurModule Y) : ℂ) * spechtCharacter Y p) := by sorry

end KWSpectrum.Estimator
