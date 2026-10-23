-- Prove2me | Theorems.Thm_MultiLayerCake_LongKnives_lemma_3
-- name    : MultiLayerCake.LongKnives.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:40.604078+00:00
-- url     : https://prove2.me/theorems/c9d7aedd-d98e-479d-83b3-bf86afbf4851
-- title:
--   Lemma 3, p. 8 — the encoding is continuous: x^{(t)} → x^{(∞)} implies A(x^{(t)}) → A(x^{(∞)})
-- statement:
--   Let $G$ be a finite additive group of order $q$, $\mathfrak P$ an equivariant procedure and $h:[m]\to G$ injective, and let $\mathcal A(x)$ be the multi-division encoded by a point $x$ of $\|\Delta_{2q-1,q}\|$. If $(x^{(t)})_{t\in\mathbb Z_+}$ is a sequence of points of $\|\Delta_{2q-1,q}\|$ converging to $x^{(\infty)}\in\|\Delta_{2q-1,q}\|$, then
--   $$\mathcal A(x^{(t)})\longrightarrow\mathcal A(x^{(\infty)}),$$
--   that is, for every bundle $g\in G$, $d\big(\mathcal A_g(x^{(t)}),\mathcal A_g(x^{(\infty)})\big)\to0$, where $d(\mathcal L,\mathcal L')=\mu(\mathcal L\triangle\mathcal L')$ is the pseudo-metric of the model.
--
--   Together with closed preferences this is what passes the approximate envy-freeness of finer and finer triangulations to the limit in the proof of Theorem 1.
--
--   **Formalization Note.** Convergence of points is in the product topology of $\mathbb R^{[2q-1]\times G}$; convergence of multi-divisions is `Converges` of the Model (each entry converges for `pdist`).
-- source:
--   Igarashi, Meunier, Envy-Free Division of Multi-Layered Cakes, arXiv:2106.02262v4, p. 8, Lemma 3

import Mathlib
import Definitions.Def_MultiLayerCake_LongKnives_Model

namespace MultiLayerCake.LongKnives

/-- Lemma 3, p. 8: the encoding is continuous — if points `x⁽ᵗ⁾` of `‖Δ_{2q−1,q}‖` converge to
`x⁽∞⁾ ∈ ‖Δ_{2q−1,q}‖`, then the multi-divisions `A(x⁽ᵗ⁾)` converge to `A(x⁽∞⁾)` for the
pseudo-metric `d`. -/
theorem lemma_3 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {m : ℕ}
    (𝔓 : Procedure G) (h : Fin m → G) (hh : Function.Injective h)
    (x : ℕ → V G → ℝ) (xInf : V G → ℝ) (hx : ∀ t, x t ∈ chessboard G)
    (hxInf : xInf ∈ chessboard G) (hlim : Filter.Tendsto x Filter.atTop (nhds xInf)) :
    Converges (fun t => encode 𝔓 h (x t)) (encode 𝔓 h xInf) := by sorry

end MultiLayerCake.LongKnives
