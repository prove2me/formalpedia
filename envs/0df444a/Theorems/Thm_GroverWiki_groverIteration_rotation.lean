-- Prove2me | Theorems.Thm_GroverWiki_groverIteration_rotation
-- name    : GroverWiki.groverIteration_rotation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T14:38:40.429295+00:00
-- url     : https://prove2.me/theorems/c65a4150-4d96-487b-baac-12375fa0fa68
-- title:
--   Each Grover iteration $U_sU_\omega$ rotates the plane by $\theta = 2\arcsin(1/\sqrt N)$
-- statement:
--   Let $N \ge 2$, let $f\colon\{0,\dots,N-1\}\to\{0,1\}$ have exactly one index $\omega$ with $f(\omega) = 1$, let $|s'\rangle = \frac{1}{\sqrt{N-1}}\sum_{x\ne\omega}|x\rangle$, and let $\theta = 2\arcsin\frac{1}{\sqrt N}$. Then for every angle $\varphi \in \mathbb R$,
--
--   $$U_sU_\omega\bigl(\cos\varphi\,|s'\rangle + \sin\varphi\,|\omega\rangle\bigr) = \cos(\varphi+\theta)\,|s'\rangle + \sin(\varphi+\theta)\,|\omega\rangle .$$
--
--   In the orthonormal basis $\{|s'\rangle, |\omega\rangle\}$ of the plane, one Grover iteration is the rotation by the angle $\theta$ towards $|\omega\rangle$.
-- source:
--   Wikipedia, "Grover's algorithm", revision oldid=1373498442, https://en.wikipedia.org/w/index.php?title=Grover%27s_algorithm&oldid=1373498442, section "Geometric proof" (PDF p. 5)

import Mathlib
import Definitions.Def_GroverWiki_Defs

open Matrix

namespace GroverWiki

/-- The Grover iteration `U_s U_ω` rotates every state `cos φ |s'⟩ + sin φ |ω⟩` of the plane
by the angle `θ = 2 arcsin(1/√N)`. -/
theorem groverIteration_rotation {N : ℕ} (hN : 2 ≤ N) (f : Fin N → Fin 2) (ω : Fin N)
    (hω : ∀ x, f x = 1 ↔ x = ω) (φ : ℝ) :
    groverIteration f *ᵥ
        ((Real.cos φ : ℂ) • perpState ω + (Real.sin φ : ℂ) • ket ω) =
      (Real.cos (φ + 2 * Real.arcsin (1 / Real.sqrt N)) : ℂ) • perpState ω +
        (Real.sin (φ + 2 * Real.arcsin (1 / Real.sqrt N)) : ℂ) • ket ω := by sorry

end GroverWiki
