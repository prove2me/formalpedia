-- Prove2me | Theorems.Thm_KawasakiSOS_Threshold_encoding_lemma
-- name    : KawasakiSOS.Threshold.encoding_lemma
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:05:24.050019+00:00
-- url     : https://prove2.me/theorems/63d3aa41-c7c5-49f4-b23d-42bb805693cc
-- title:
--   Lemma 2.4: the encoding lemma
-- statement:
--   Let $k\ge3$ and $\lambda>1$, write $\mu=\lambda^{-2}$, and let $(\gamma_{xy})$ be a system of paths of the Kawasaki chain. Suppose that for every transition $e=(z,z')$ with $z\ne z'$ there is an injective map
--
--   $$\eta_e:\{(x,y):e\in\gamma_{xy}\}\to\Omega\times S_e,\qquad |S_e|\le N,$$
--
--   such that $\eta_e(x,y)=(w,s)$ implies
--
--   $$\max\{M(z),M(z')\}+M(w)\le M(x)+M(y)+c.\tag{2}$$
--
--   Then $\rho\le2k\,\mu^{-c}N$.
--
--   The lemma reduces a congestion bound to a counting problem: each pair using a transition is assigned a complementary configuration and bounded side information, and the stationary weight of the complementary configuration pays for the pair.
--
--   Differences from the source:
--   - encoding: paths of transitions, assumed simple → walks with no step (z, z); reason: the transitions of the lemma have z ≠ z′; a simple path has no such step, and the hypothesis is the only part of simplicity used
--   - encoding: N a size bound on S_e → N a real number, S_e any finite type in Type; reason: every finite set is equivalent to one in Type; a real bound includes the integer ones
--   - encoding: pairs (x, y) with e ∈ γ_xy → pairs with x ≠ y and e ∈ γ_xy; reason: a simple path from x to x has no edges, so no pair with x = y uses a transition
--   - encoding: the constant c, unrestricted → c a real number, μ^{−c} a real power; reason: every value of c the source can mean is a real number; c = 2 is the case used
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 2.4, p. 6 (PDF p. 7)

import Mathlib
import Definitions.Def_DiaconisStroock_Poincare_Paths
import Definitions.Def_DiaconisStroock_CanonPaths_Eta
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_energy
import Definitions.Def_KawasakiSOS_Threshold_gibbs
import Definitions.Def_KawasakiSOS_Threshold_kawasaki
import Definitions.Def_KawasakiSOS_Threshold_mu
open MarkovMixing DiaconisStroock.Poincare DiaconisStroock.CanonPaths

namespace KawasakiSOS.Threshold

/-- Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 2.4, p. 6 (PDF p. 7).

Formalization Notes:
- encoding: paths of transitions, assumed simple → walks with no step (z, z). The transitions of the lemma have z ≠ z′; a simple path has no such step, and the hypothesis is the only part of simplicity used.
- encoding: N a size bound on S_e → N a real number, S_e any finite type in Type. Every finite set is equivalent to one in Type; a real bound includes the integer ones.
- encoding: pairs (x, y) with e ∈ γ_xy → pairs with x ≠ y and e ∈ γ_xy. A simple path from x to x has no edges, so no pair with x = y uses a transition.
- encoding: the constant c, unrestricted → c a real number, μ^{−c} a real power. Every value of c the source can mean is a real number; c = 2 is the case used. -/
theorem encoding_lemma {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (hkn : k ≤ n) {lam : ℝ} (hlam : 1 < lam) (γ : Config n k → Config n k → List (Config n k)) (hγ : IsWalkSystem (kawasaki n k lam) (gibbs n k lam) γ) (hloop : ∀ x y, x ≠ y → ∀ e ∈ pathEdges (γ x y), e.1 ≠ e.2) (c : ℝ) (N : ℝ)
    (henc : ∀ e : Config n k × Config n k, e.1 ≠ e.2 → 0 < kawasaki n k lam e.1 e.2 →
      ∃ (S : Type) (_ : Fintype S)
        (η : {p : Config n k × Config n k // p.1 ≠ p.2 ∧ e ∈ pathEdges (γ p.1 p.2)} → Config n k × S),
        (Fintype.card S : ℝ) ≤ N ∧ Function.Injective η ∧
          ∀ p, ((max (energy e.1.1) (energy e.2.1) : ℕ) : ℝ) + (energy (η p).1.1 : ℝ) ≤
            (energy p.1.1.1 : ℝ) + (energy p.1.2.1 : ℝ) + c) :
    eta (kawasaki n k lam) (gibbs n k lam) γ ≤ 2 * (k : ℝ) * (mu lam)⁻¹ ^ c * N := by sorry

end KawasakiSOS.Threshold
