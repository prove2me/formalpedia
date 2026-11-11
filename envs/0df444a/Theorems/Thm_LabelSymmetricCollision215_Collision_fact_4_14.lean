-- Prove2me | Theorems.Thm_LabelSymmetricCollision215_Collision_fact_4_14
-- name    : LabelSymmetricCollision215.Collision.fact_4_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:59:03.959099+00:00
-- url     : https://prove2.me/theorems/4726f5d6-1620-4c56-bea0-21f1f5833f8a
-- title:
--   Fact 4.14 — Equivariant image forces a large orbit
-- statement:
--   Let $V$ be any finite-dimensional complex representation of the symmetric group on $N$ range labels, $v\in V$, and $\lambda\vdash N$. If $B:V\to S^\lambda$ is equivariant and $B(v)\ne0$, then
--   $$\dim\operatorname{span}\{\sigma v:\sigma\in S_N\}\ge\dim S^\lambda.$$
--   This applies an actual Specht target to the orbit of an arbitrary vector.
--
--   Differences from the source:
--   - encoding: complex Specht modules and standard-tableau multiplicities → published Young left ideals and increasing bijective fillings, transported to cyclic range labels; reason: these are concrete realizations of the same representations and multiplicity sets; height caps exclude no partition of the specified size
-- source:
--   Frédéric Magniez, Sebastian Zur, Tight Time-Space Lower Bounds for Collision Finding and Element Distinctness under Label Symmetry, STOC 2027 submission #215 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/215.pdf, Fact 4.14, PDF 30 / printed 28

import Definitions.Def_LabelSymmetricCollision215_Collision_Specht

namespace LabelSymmetricCollision215.Collision

/-- Magniez–Zur, Fact 4.14, PDF 30 / printed 28. -/
theorem fact_4_14 {N : ℕ} [NeZero N] {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (ZMod N)) V) (v : V) (lam : Shape N)
    (B : V →ₗ[ℂ] Specht lam)
    (hequiv : ∀ σ u, B (ρ σ u) = spechtAction lam σ (B u)) (hB : B v ≠ 0) :
    Module.finrank ℂ (Specht lam) ≤ Module.finrank ℂ (orbitSpan (fun σ => ρ σ) v) := by sorry

end LabelSymmetricCollision215.Collision
