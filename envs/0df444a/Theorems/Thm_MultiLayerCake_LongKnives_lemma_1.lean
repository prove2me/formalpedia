-- Prove2me | Theorems.Thm_MultiLayerCake_LongKnives_lemma_1
-- name    : MultiLayerCake.LongKnives.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:42.553218+00:00
-- url     : https://prove2.me/theorems/3b513b0f-633a-45d4-b798-d7b51f574e15
-- title:
--   Lemma 1, p. 6 — for G = ((ℤ_p)^k, +), every G-equivariant continuous map ‖Δ_{2q−1,q}‖ → Δ^G hits the barycenter
-- statement:
--   Let $q=p^k$ with $p$ prime and $k\ge1$, and let $G=((\mathbb Z_p)^k,+)$. Let $\Delta_{2q-1,q}$ be the chessboard complex on $[2q-1]\times G$, with $G$ acting by $g\cdot(r,j)=(r,g+j)$, and let $\Delta^G\subseteq\mathbb R^G$ be the standard simplex with vertices $e_g$, on which $G$ acts by $g'\cdot e_g=e_{g+g'}$. For every continuous map $f:\|\Delta_{2q-1,q}\|\to\Delta^G$ that is $G$-equivariant, $f(g\cdot x)=g\cdot f(x)$, there is $x_0\in\|\Delta_{2q-1,q}\|$ with
--   $$f(x_0)=\frac1q\sum_{g\in G}e_g .$$
--
--   This is the topological half of the proof of Theorem 1: the average of the agents' approximate preferences is such an equivariant map, and the point $x_0$ where it equals the barycenter yields a fractional assignment in which every bundle is equally popular. It is a consequence of Volovikov's theorem and the $(q-2)$-connectivity of the chessboard complex.
--
--   **Formalization Note.** The realization $\|\Delta_{2q-1,q}\|$ is the explicit subset of $\mathbb R^{[2q-1]\times G}$ defined in the Model; $f$ is a function on the ambient space whose continuity, range and equivariance are asked on that subset only. The barycenter is the constant vector $1/p^k$.
-- source:
--   Igarashi, Meunier, Envy-Free Division of Multi-Layered Cakes, arXiv:2106.02262v4, p. 6, Lemma 1

import Mathlib
import Definitions.Def_MultiLayerCake_LongKnives_Model

namespace MultiLayerCake.LongKnives

/-- Lemma 1, p. 6: for `q = p^k` (`p` prime, `k ≥ 1`) and `G = ((ℤ_p)^k, +)`, every `G`-equivariant
continuous map `f : ‖Δ_{2q−1,q}‖ → Δ^G` hits the barycenter `(1/q) Σ_{g∈G} e_g` of `Δ^G`. -/
theorem lemma_1 (p k : ℕ) [Fact p.Prime] (hk : 0 < k)
    (f : (V (Fin k → ZMod p) → ℝ) → ((Fin k → ZMod p) → ℝ))
    (hcont : ContinuousOn f (chessboard (Fin k → ZMod p)))
    (hmaps : Set.MapsTo f (chessboard (Fin k → ZMod p)) (stdSimplex ℝ (Fin k → ZMod p)))
    (hequiv : ∀ g : Fin k → ZMod p, ∀ x ∈ chessboard (Fin k → ZMod p),
      f (actCB g x) = actSimplex g (f x)) :
    ∃ x₀ ∈ chessboard (Fin k → ZMod p), f x₀ = fun _ => 1 / ((p : ℝ) ^ k) := by sorry

end MultiLayerCake.LongKnives
