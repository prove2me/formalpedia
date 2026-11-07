-- Prove2me | Theorems.Thm_HeilmanMax3Cut_lemma_8_3
-- name    : HeilmanMax3Cut.lemma_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:28:06.424204+00:00
-- url     : https://prove2.me/theorems/2b08bcee-530b-46f6-a233-e2b863eddbe1
-- title:
--   Lemma 8.3 — first-mode endpoint gain
-- statement:
--   Let $K^{(1)}(p,q)=\int_0^p\int_0^q\frac12[r^{(1)}(u-v)+r^{(1)}(u+v)]\,dv\,du$ with $r^{(1)}(u)=1-\cos(\pi u)$, and $j^{(1)}=(9-\sqrt3\pi)/(4\pi^2)$, $\tau^{(1)}=1+(9-4\sqrt3\pi)/(4\pi^2)$ (85). For every $p,q\in\Delta_3$, with $b=1/3$, $x=p-b\mathbf 1$ and $y=q-b\mathbf 1$,
--
--   $$\sum_{i=1}^3K^{(1)}(p_i,q_i)-3K^{(1)}(b,b)\ \ge\ \bigl(\tau^{(1)}+2j^{(1)}\bigr)\langle x,y\rangle+\tfrac32\,j^{(1)}\bigl(\|x\|^2+\|y\|^2\bigr).$$
--
--   This improves the homogeneous bound (84) for the first angular mode and produces the gain $\theta(a)$ of Corollary 8.4.
--
--   Differences from the source:
--   - encoding: x = p − b1, y = q − b1 in ℝ³ with ⟨x, y⟩ and ‖x‖² → functions Fin 3 → ℝ with ∑ᵢ (pᵢ − 1/3)(qᵢ − 1/3) and ∑ᵢ (pᵢ − 1/3)²; reason: the same Euclidean quantities written in coordinates
--   - encoding: j^{(1)} := j_{r^{(1)}} and τ^{(1)} := τ_{r^{(1)}} of (83), with the values printed in (85) → j1, tau1 defined by the closed forms of (85); reason: the paper states these closed forms as their values (and they agree with (83))
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Lemma 8.3, Eq. (89), p.28

import Mathlib
import Definitions.Def_HeilmanMax3Cut_Delta3
import Definitions.Def_HeilmanMax3Cut_K1
import Definitions.Def_HeilmanMax3Cut_j1
import Definitions.Def_HeilmanMax3Cut_tau1

namespace HeilmanMax3Cut

/-- **Lemma 8.3 (first-mode endpoint gain).** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Lemma 8.3, Eq. (89), p.28: "For any
`p, q ∈ Δ₃`, put `x := p − b1` and `y := q − b1`. Then
`∑_{i=1}^3 K^{(1)}(pᵢ, qᵢ) − 3K^{(1)}(b, b) ≥ (τ^{(1)} + 2j^{(1)})⟨x, y⟩ + (3/2) j^{(1)}(‖x‖² + ‖y‖²)`",
with `b = 1/3`, `K^{(1)}` from (82)/(86) and `τ^{(1)}, j^{(1)}` from (85).

**Formalization Note.** `⟨x, y⟩ = ∑ᵢ xᵢyᵢ`, `‖x‖² = ∑ᵢ xᵢ²`. -/
theorem lemma_8_3 :
    ∀ p ∈ Delta3, ∀ q ∈ Delta3,
      (tau1 + 2 * j1) * (∑ i, (p i - 1 / 3) * (q i - 1 / 3)) +
          3 / 2 * j1 * (∑ i, (p i - 1 / 3) ^ 2 + ∑ i, (q i - 1 / 3) ^ 2) ≤
        ∑ i, K1 (p i) (q i) - 3 * K1 (1 / 3) (1 / 3) := by sorry

end HeilmanMax3Cut
