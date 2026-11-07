-- Prove2me | Theorems.Thm_MetricMSO_theorem_1_6
-- name    : MetricMSO.theorem_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:44:38.489281+00:00
-- url     : https://prove2.me/theorems/b135450c-12a4-4b94-ad1f-6d904b2febec
-- title:
--   Theorem 1.6 — $\mathsf{EqGC}$ is $\mathrm{MSO}_1$-definable on graphs with $\mathrm{cbl}(G)<M$
-- statement:
--   For every integer $M\ge3$, the $\mathrm{MSO}_1$ formula $\mathsf{CertEqGC}_M(C,x,y,u,v)$ of p.28 has length polynomial in $M$, and on every graph $G$ with $\mathrm{cbl}(G)<M$ it is equivalent to $\mathsf{EqGC}(C,x,y,u,v)$.
--
--   **Formalization Note** The length bound is $c\,(M+1)^c$ with one constant $c$ for all $M$.
--
--   Differences from the source:
--   - generalization: there exists an MSO1 formula CertEqGC_M → the paper's own formula of p.28, as the Lean definition certEqGC; reason: an explicit witness implies the existence claim, and Lemma 4.3 needs the explicit formula
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), Theorem 1.6, p.7 (PDF 9), restated p.24 (PDF 26); the formula is on p.28 (PDF 30)

import Mathlib
import Definitions.Def_MetricMSO_Sat
import Definitions.Def_MetricMSO_cbl
import Definitions.Def_MetricMSO_IsCMSO1
import Definitions.Def_MetricMSO_certEqGC

namespace MetricMSO

/-- **Theorem 1.6.** Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), p.7 (PDF 9), restated p.24 (PDF 26): "For
every integer M ≥ 3, there exists an MSO1 formula CertEqGCM(C, x, y, u, v) of length polynomial in M
that, on every graph G with cbl(G) < M, is equivalent to EqGC(C, x, y, u, v)."

**Formalization Note** Stated for the paper's own formula, p.28 (PDF 30): `certEqGC M 0 0 1 2 3 4 1` is
`CertEqGC_M(C, x, y, u, v)` in the context of the vertex variables `x, y, u, v` (levels 0–3) and the set
variable `C` (level 0). "Polynomial in M" is `≤ c · (M + 1)^c` with one `c` for all `M`. -/
theorem theorem_1_6 :
    ∃ c : ℕ, ∀ M : ℕ, 3 ≤ M →
      IsMSO1 (certEqGC M 0 0 1 2 3 4 1) ∧
      (certEqGC M 0 0 1 2 3 4 1).length ≤ c * (M + 1) ^ c ∧
      ∀ I : Instance, cbl I.G < M → ∀ (C : Finset (Fin I.n)) (x y u v : Fin I.n),
        (Sat I ⟨[x, y, u, v], [], [C], []⟩ (certEqGC M 0 0 1 2 3 4 1) ↔ EqGC I.G C x y u v) := by sorry

end MetricMSO
