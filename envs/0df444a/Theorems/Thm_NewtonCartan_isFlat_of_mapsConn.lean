-- Prove2me | Theorems.Thm_NewtonCartan_isFlat_of_mapsConn
-- name    : NewtonCartan.isFlat_of_mapsConn
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-21T18:12:54.41004+00:00
-- url     : https://prove2.me/theorems/b00a2322-c77f-47fc-950a-d01e1b569b52
-- title:
--   Curvature naturality: a derivative operator mapped by a diffeomorphism to a flat one is flat
-- statement:
--   Let $f:\mathbb R^4\to\mathbb R^4$ be a diffeomorphism and let $\nabla$, $\nabla'$ be smooth torsion-free derivative operators (Christoffel symbols $\Gamma$, $\Gamma'$) such that $f_*\nabla=\nabla'$, i.e. $\partial_b\partial_c f^a+\Gamma'^a_{de}(f(x))\,\partial_b f^d\,\partial_c f^e=\partial_n f^a\,\Gamma^n_{bc}(x)$. If $\nabla'$ is flat ($R'^a{}_{bcd}=0$), then $\nabla$ is flat. This is the naturality of the Riemann tensor under diffeomorphisms: $\partial_n f^a\,R^n{}_{bcd}(x)=R'^a{}_{pqm}(f(x))\,\partial_b f^p\,\partial_c f^q\,\partial_d f^m$, together with invertibility of the Jacobian of $f$.
-- source:
--   Weatherall 2016, Are Newtonian gravitation and geometrized Newtonian gravitation theoretically equivalent?, Erkenntnis 81, Prop. 6.1 (proof: pullbacks of flat derivative operators by diffeomorphisms are flat); standard naturality of curvature, e.g. Malament, Topics in the Foundations of General Relativity and Newtonian Gravitation Theory, Sect. 1.9.

import Definitions.Def_NewtonCartan_defs

open scoped ContDiff

namespace NewtonCartan

/-- Naturality of curvature: if the diffeomorphism `f` maps the derivative operator `Γ` to the flat
derivative operator `Γ'` (`f_* ∇ = ∇'`, transformation law `MapsConn`), then `Γ` is flat. -/
theorem isFlat_of_mapsConn (f : E ≃ E) (hf : IsDiffeo f) (Γ Γ' : Conn) (hΓ : IsDerivOp Γ)
    (hΓ' : IsDerivOp Γ') (hm : MapsConn f Γ Γ') (hfl : IsFlat Γ') : IsFlat Γ := by sorry

end NewtonCartan
