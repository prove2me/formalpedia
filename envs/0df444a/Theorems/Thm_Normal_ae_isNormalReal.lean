-- Prove2me | Theorems.Thm_Normal_ae_isNormalReal
-- name    : Normal.ae_isNormalReal
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-07T12:44:56.982706+00:00
-- url     : https://prove2.me/theorems/3d5ca33d-2b3c-4a74-8068-aea31e268a95
-- title:
--   Borel's normal number theorem: almost every real is absolutely normal
-- statement:
--   Let $\lambda$ be Lebesgue measure on $\mathbb R$ and $d_b(x,n)=\lfloor x\,b^{n+1}\rfloor\bmod b$. **Theorem.** For $\lambda$-almost every real $x$, $x$ is normal in every base $b\ge 2$ simultaneously: for all $b\ge 2$ and every word $w$ of length $k$ over $\{0,\dots,b-1\}$,
--   $$\lim_{N\to\infty}\frac{\#\{\,i<N : d_b(x,i+j)=w_j \text{ for all } j<k\,\}}{N}=b^{-k}.$$
--   A single null exceptional set serves all bases.
-- source:
--   É. Borel, Les probabilités dénombrables et leurs applications arithmétiques, Rend. Circ. Mat. Palermo 27 (1909), 247–271.

import Mathlib
import Definitions.Def_Normal_Core

namespace Normal

theorem ae_isNormalReal :
    ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∀ b : ℕ, 2 ≤ b → IsNormalReal b x := by sorry

end Normal
