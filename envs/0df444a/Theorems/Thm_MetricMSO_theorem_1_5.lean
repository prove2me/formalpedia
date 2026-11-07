-- Prove2me | Theorems.Thm_MetricMSO_theorem_1_5
-- name    : MetricMSO.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:43:26.324475+00:00
-- url     : https://prove2.me/theorems/3de2de92-51e5-495f-8c69-d443f8fef238
-- title:
--   Theorem 1.5 — $\mathsf{SP}$ is $\mathrm{MSO}_1$-definable on graphs with $\mathrm{cbl}(G)<M$
-- statement:
--   For every integer $M\ge3$, the $\mathrm{MSO}_1$ formula $\mathsf{CertSP}_M(P,x,y)$ of eq. (5) has length polynomial in $M$, and on every graph $G$ with $\mathrm{cbl}(G)<M$ it is equivalent to $\mathsf{SP}(P,x,y)$:
--   $$G\models\mathsf{CertSP}_M(P,x,y)\iff P\text{ is a shortest }x\text{-}y\text{ path set}.$$
--
--   **Formalization Note** The length bound is $c\,(M+1)^c$ with one constant $c$ for all $M$.
--
--   Differences from the source:
--   - generalization: there exists an MSO1 formula CertSP_M → the paper's own formula of eq. (5), as the Lean definition certSP; reason: an explicit witness implies the existence claim, and Lemma 4.3 needs the explicit formula
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), Theorem 1.5, p.6 (PDF 8), restated p.19 (PDF 21); the formula is eq. (5), p.23 (PDF 25)

import Mathlib
import Definitions.Def_MetricMSO_Sat
import Definitions.Def_MetricMSO_cbl
import Definitions.Def_MetricMSO_IsCMSO1
import Definitions.Def_MetricMSO_certSP

namespace MetricMSO

/-- **Theorem 1.5.** Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), p.6 (PDF 8), restated p.19 (PDF 21): "For
every integer M ≥ 3, there exists an MSO1 formula CertSPM(P, x, y) of length polynomial in M that, on
every graph G with cbl(G) < M, is equivalent to SP(P, x, y)."

**Formalization Note** Stated for the paper's own formula, eq. (5), p.23 (PDF 25): `certSP M 0 0 1 2 1`
is `CertSP_M(P, x, y)` in the context of the vertex variables `x, y` (levels 0, 1) and the set variable
`P` (level 0). "Polynomial in M" is `≤ c · (M + 1)^c` with one `c` for all `M`. -/
theorem theorem_1_5 :
    ∃ c : ℕ, ∀ M : ℕ, 3 ≤ M →
      IsMSO1 (certSP M 0 0 1 2 1) ∧
      (certSP M 0 0 1 2 1).length ≤ c * (M + 1) ^ c ∧
      ∀ I : Instance, cbl I.G < M → ∀ (P : Finset (Fin I.n)) (x y : Fin I.n),
        (Sat I ⟨[x, y], [], [P], []⟩ (certSP M 0 0 1 2 1) ↔ IsShortestPathSet I.G P x y) := by sorry

end MetricMSO
