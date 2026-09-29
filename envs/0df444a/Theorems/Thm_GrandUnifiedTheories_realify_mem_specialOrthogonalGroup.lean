-- Prove2me | Theorems.Thm_GrandUnifiedTheories_realify_mem_specialOrthogonalGroup
-- name    : GrandUnifiedTheories.realify_mem_specialOrthogonalGroup
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T01:01:52.036247+00:00
-- url     : https://prove2.me/theorems/45b430e5-c765-40be-be40-0619954c814a
-- title:
--   $\rho$ carries $\mathrm{SU}(5)$ into $\mathrm{SO}(10)$
-- statement:
--   If a complex $5\times5$ matrix $A$ is unitary with determinant one, then its realification $\rho(A)$ is a real $10\times10$ matrix that is orthogonal with determinant one:
--
--   $$A\in\mathrm{SU}(5)\ \Longrightarrow\ \rho(A)\in\mathrm{SO}(10).$$
--
--   Orthogonality reflects that a unitary map preserves the real part of the Hermitian inner product, which is the Euclidean inner product of $\mathbb{R}^{10}$. The determinant statement is the general identity $\det_{\mathbb{R}}\rho(A) = |\det_{\mathbb{C}} A|^{2}$, which equals one for any unitary $A$ — so in fact the whole of $\mathrm{U}(5)$, not just $\mathrm{SU}(5)$, lands in $\mathrm{SO}(10)$, as the source observes.
-- source:
--   John Baez and John Huerta, The Algebra of Grand Unified Theories, https://math.ucr.edu/home/baez/guts.pdf, Section 4, p. 68 (proof of Theorem 8: 'We can consider the subgroup of SO(10) that preserves the original complex structure. This is U(5) ⊆ SO(10). If we further pick a volume form ... we get a copy of SU(5) ⊆ SO(10)')

import Mathlib
import Definitions.Def_GUT_standard_model_group
import Definitions.Def_GUT_realification

namespace GrandUnifiedTheories

theorem realify_mem_specialOrthogonalGroup (A : Matrix Idx5 Idx5 ℂ)
    (hA : A ∈ Matrix.specialUnitaryGroup Idx5 ℂ) :
    realify A ∈ Matrix.specialOrthogonalGroup Idx10 ℝ := by sorry

end GrandUnifiedTheories
