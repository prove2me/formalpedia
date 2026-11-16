-- Prove2me | Theorems.Thm_MatrixSpencer_Supplement_theorem_1_5
-- name    : MatrixSpencer.Supplement.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T19:31:03.44446+00:00
-- url     : https://prove2.me/theorems/8365cdbd-52e4-43c4-910e-f493a6d5ff47
-- title:
--   Theorem 1.5 (Matrix small ball) — $\mathbb P\{\|\sum_i g_iA_i\|<4\}\ge e^{-cd}$ with $c=-8\log\frac{1020\sqrt3-1671}{128}-\log\frac34\approx2.614861$
-- statement:
--   Let $n,d\ge1$ be integers and let $A_1,\dots,A_n$ be symmetric $d\times d$ matrices with
--   $$\mathbb E X^2=\sum_{i=1}^nA_i^2\preceq I_d,$$
--   where $X=\sum_{i=1}^n g_iA_i$ and $g=(g_1,\dots,g_n)$ has independent standard Gaussian coordinates. Then
--   $$\mathbb P\Bigl\{\Bigl\|\sum_{i=1}^ng_iA_i\Bigr\|<4\Bigr\}\ \ge\ e^{-cd},\qquad c=-8\log\Bigl(\frac{1020\sqrt3-1671}{128}\Bigr)-\log\Bigl(\frac34\Bigr)\approx2.614861,$$
--   where $\|\cdot\|$ is the operator norm. In particular there are universal constants $C,c>0$ with $\mathbb P\{\|X\|<C\}\ge e^{-cd}$.
--
--   This is the non-hereditary matrix small-ball estimate: a Gaussian matrix series of unit matrix variance lies in a ball of constant radius with probability exponential only in the dimension, with no logarithmic loss.
--
--   **Formalization Note** The statement fixes the constants the paper gives, $C=4$ and the exact $c$ from the last display of the proof (p.26); this implies the existential form since $c>0$. $\sum_iA_i^2\preceq I_d$ means $I_d-\sum_iA_i^2$ is positive semidefinite.
--
--   Differences from the source:
--   - reading: "there exist universal constants C, c > 0 … In particular C = 4 and c ≈ 2.614861" → C = 4 and c = −8 log((1020√3 − 1671)/128) − log(3/4); reason: the "in particular" clause is the stronger form and implies the existential one (c > 0 holds); "≈ 2.614861" is the decimal of the exact value the proof derives on p.26 (PDF p.28)
--   - encoding: EX² = ∑ᵢ Aᵢ² ⪯ I_d → I − ∑ᵢ Aᵢ² positive semidefinite; reason: Loewner order; EX² = ∑ᵢ Aᵢ² is an identity, not a hypothesis
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 1.5, p.2 (PDF p.4); exact constant: proof of Theorem 1.5, eq. (B.47) and the following display, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_MatrixSpencer_gam
import Definitions.Def_MatrixSpencer_series
open scoped Matrix.Norms.L2Operator

namespace MatrixSpencer.Supplement

/-- **Theorem 1.5 (Matrix small ball).**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…),
Theorem 1.5, p.2 (PDF p.4): "Let n, d ≥ 1 be integers, and let X = ∑ⁿᵢ₌₁ gᵢAᵢ be a d × d symmetric
random Gaussian matrix with EX² = ∑ⁿᵢ₌₁ Aᵢ² ⪯ I_d. Then there exist universal constants C, c > 0
such that P{‖X‖ < C} ≥ exp(−cd). In particular, the absolute constants can be chosen to satisfy
C = 4 and c ≈ 2.614861." The exact `c` is the last display of the proof, p.26 (PDF p.28):
`c = −8 log((1020√3 − 1671)/128) − log(3/4)`.

**Formalization Note.** The statement is given with the explicit constants `C = 4` and the exact
`c` above, which implies the existential form (`c > 0` is proved in the verification file).
`‖·‖` is the operator norm; `g ∼ γₙ`; `⪯` is positive semidefiniteness of `I − ∑ᵢ Aᵢ²`. -/
theorem theorem_1_5 {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d) (A : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ i, (A i).IsSymm) (hAA : (1 - ∑ i, A i ^ 2).PosSemidef) :
    Real.exp (-((-8 * Real.log ((1020 * √3 - 1671) / 128) - Real.log (3 / 4)) * d)) ≤
      (gam n).real {g | ‖series A g‖ < 4} := by sorry

end MatrixSpencer.Supplement
