-- Prove2me | Theorems.Thm_IsotropicSpin_spectrum_half
-- name    : IsotropicSpin.spectrum_half
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T04:24:58.28634+00:00
-- url     : https://prove2.me/theorems/061b2a89-a958-481e-a034-4b802799090f
-- title:
--   Every output $\Lambda_{1/2}(|\phi\rangle\langle\phi|)$ has spectrum $(1/3,2/3)$
-- statement:
--   Let $\Lambda_{1/2}$ be the isotropic spin-1/2 channel (6). For every unit vector $\phi\in\mathbb C^2$, the output $\Lambda_{1/2}(|\phi\rangle\langle\phi|)$ has eigenvalues $1/3$ and $2/3$, each with multiplicity one:
--
--   $$
--   \det\big(\lambda\mathbf 1-\Lambda_{1/2}(|\phi\rangle\langle\phi|)\big)=\Big(\lambda-\frac13\Big)\Big(\lambda-\frac23\Big).
--   $$
--
--   Hence every pure input gives the output entropy $\log3-\tfrac23\log2$, the value (9).
--
--   **Formalization Note** The spectrum is stated basis-free through the characteristic polynomial over $\mathbb C$.
--
--   Differences from the source:
--   - encoding: spectrum (1/3, 2/3) → charpoly = (X − 1/3)(X − 2/3); reason: a 2×2 matrix has eigenvalues 1/3, 2/3 with multiplicity exactly when this holds; same statement
-- source:
--   Alicki, Isotropic quantum spin channels and additivity questions, arXiv:quant-ph/0402080v1, §2, Case s = 1/2, sentence after (12), p.2

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model
import Definitions.Def_IsotropicSpin_spinHalf
import Definitions.Def_IsotropicSpin_isotropicChannel

open Polynomial

namespace IsotropicSpin

/-- **Every pure-input output of `Λ_{1/2}` has spectrum `(1/3, 2/3)`**, Alicki,
arXiv:quant-ph/0402080v1, §2, Case s = 1/2, p. 2 (sentence after (12)): "all density matrices
`Λ_{1/2}(|φ⟩⟨φ|)` possess the same spectrum `(1/3, 2/3)`".

**Formalization Note** The spectrum with multiplicities is stated basis-free through the
characteristic polynomial: `det(λ𝟙 − Λ_{1/2}(|φ⟩⟨φ|)) = (λ − 1/3)(λ − 2/3)` for every unit vector
`φ ∈ ℂ²`. `pureState φ = |φ⟩⟨φ|` and `IsUnitVector` are from the published bundle
`WHAdditivity.Renyi`. -/
theorem spectrum_half (φ : Fin 2 → ℂ) (hφ : WHAdditivity.Renyi.IsUnitVector φ) :
    (isotropicChannel (1 / 2) spinHalf (WHAdditivity.Renyi.pureState φ)).charpoly =
      (X - C (1 / 3 : ℂ)) * (X - C (2 / 3 : ℂ)) := by sorry

end IsotropicSpin
