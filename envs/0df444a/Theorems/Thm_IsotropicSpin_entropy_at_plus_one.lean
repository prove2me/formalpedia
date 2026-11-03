-- Prove2me | Theorems.Thm_IsotropicSpin_entropy_at_plus_one
-- name    : IsotropicSpin.entropy_at_plus_one
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:25:46.289192+00:00
-- url     : https://prove2.me/theorems/4c7d7444-819f-4d43-ad72-76434186a2db
-- title:
--   $S(\Lambda_1(|1\rangle\langle1|))=\log2$ (p.3)
-- statement:
--   Let $\Lambda_1$ be the isotropic spin-1 channel (6) with the matrices (13), and $|1\rangle=|{+}1\rangle$ the eigenvector of $S_3$ for the eigenvalue $1$. Then
--
--   $$
--   S\big(\Lambda_1(|1\rangle\langle1|)\big)=\log 2 .
--   $$
--
--   (Explicitly, $\Lambda_1(|1\rangle\langle1|)=\operatorname{diag}(1/2,1/2,0)$.) With (14) this shows that the infimum $S[\Lambda_1]$ is attained and equals $\log 2$.
--
--   **Formalization Note** $|1\rangle$ is the first basis vector `Pi.single 0 1`, the basis order of (13).
--
--   Differences from the source:
--   - encoding: log (no base stated) → Real.log, the natural logarithm, inside the von Neumann entropy WHAdditivity.Renyi.vonNeumannEntropy (0 log 0 = 0); reason: Lean convention; every term of the statement scales by the same factor under a change of base
-- source:
--   Alicki, Isotropic quantum spin channels and additivity questions, arXiv:quant-ph/0402080v1, §2, proof of Theorem 1, last step, p.3

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model
import Definitions.Def_IsotropicSpin_spinOne
import Definitions.Def_IsotropicSpin_isotropicChannel

namespace IsotropicSpin

/-- **Attainment at `|1⟩`**, Alicki, arXiv:quant-ph/0402080v1, §2, proof of Theorem 1, p. 3: "In the
last step one can compute explicitly the matrix `Λ₁(|1⟩⟨1|)` what gives `S(Λ₁(|1⟩⟨1|)) = log 2`".

**Formalization Note** `|1⟩ = |+1⟩` is the first basis vector of (13), `Pi.single 0 1`.
`S` is the von Neumann entropy of the published bundle `WHAdditivity.Renyi` (natural logarithm). -/
theorem entropy_at_plus_one :
    WHAdditivity.Renyi.vonNeumannEntropy
        (isotropicChannel 1 spinOne (WHAdditivity.Renyi.pureState (Pi.single 0 1 : Fin 3 → ℂ))) =
      Real.log 2 := by sorry

end IsotropicSpin
