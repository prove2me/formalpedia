-- Prove2me | Theorems.Thm_HeilmanMax3Cut_corollary_8_4
-- name    : HeilmanMax3Cut.corollary_8_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:30:30.655025+00:00
-- url     : https://prove2.me/theorems/b8276592-506d-48e6-aee6-38cbfb238a9a
-- title:
--   Corollary 8.4 — joint arc bound with first-mode gain
-- statement:
--   Let $\theta(a)=\frac{j^{(1)}}2\,ae^{-a}/I_0(a)$ (92). For every $a\ge0$ and $p,q\in\Delta_3$, with $b=1/3$, $x=p-b\mathbf 1$ and $y=q-b\mathbf 1$,
--
--   $$\sum_{i=1}^3K_a(p_i,q_i)-3K_a(b,b)\ \ge\ \bigl(\tau(a)+4\theta(a)\bigr)\langle x,y\rangle+\bigl(j(a)+\theta(a)\bigr)\bigl(\|x\|^2+\|y\|^2\bigr).$$
--
--   This improves Lemma 8.1 and is the pointwise inequality integrated over the radii in the proof of Theorem 7.1.
--
--   Differences from the source:
--   - encoding: x = p − b1, y = q − b1 in ℝ³ with ⟨x, y⟩ and ‖x‖² → functions Fin 3 → ℝ with ∑ᵢ (pᵢ − 1/3)(qᵢ − 1/3) and ∑ᵢ (pᵢ − 1/3)²; reason: the same Euclidean quantities written in coordinates
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Corollary 8.4, Eq. (94), p.29

import Mathlib
import Definitions.Def_HeilmanMax3Cut_Delta3
import Definitions.Def_HeilmanMax3Cut_Karc
import Definitions.Def_HeilmanMax3Cut_tauA
import Definitions.Def_HeilmanMax3Cut_jA
import Definitions.Def_HeilmanMax3Cut_thetaG

namespace HeilmanMax3Cut

/-- **Corollary 8.4.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Corollary 8.4, Eq. (94), p.29: "For any `a ≥ 0` and `p, q ∈ Δ₃`, put
`x = p − b1` and `y = q − b1`. Then
`∑_{i=1}^3 K_a(pᵢ, qᵢ) − 3K_a(b, b) ≥ (τ(a) + 4θ(a))⟨x, y⟩ + (j(a) + θ(a))(‖x‖² + ‖y‖²)`",
with `b = 1/3` and `θ(a)` from (92).

**Formalization Note.** `⟨x, y⟩ = ∑ᵢ xᵢyᵢ`, `‖x‖² = ∑ᵢ xᵢ²`. -/
theorem corollary_8_4 :
    ∀ a : ℝ, 0 ≤ a → ∀ p ∈ Delta3, ∀ q ∈ Delta3,
      (tauA a + 4 * thetaG a) * (∑ i, (p i - 1 / 3) * (q i - 1 / 3)) +
          (jA a + thetaG a) * (∑ i, (p i - 1 / 3) ^ 2 + ∑ i, (q i - 1 / 3) ^ 2) ≤
        ∑ i, Karc a (p i) (q i) - 3 * Karc a (1 / 3) (1 / 3) := by sorry

end HeilmanMax3Cut
