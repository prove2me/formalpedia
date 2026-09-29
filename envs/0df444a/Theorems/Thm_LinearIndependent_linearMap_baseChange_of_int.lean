-- Prove2me | Theorems.Thm_LinearIndependent_linearMap_baseChange_of_int
-- name    : LinearIndependent.linearMap_baseChange_of_int
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/c160ace1-a05d-50e3-a98f-202a2d765709
-- title:
--   Base change to a characteristic-zero field preserves independence of endomorphisms
-- statement:
--   Let $K$ be a field of characteristic zero, and let $\Lambda$ be an abelian group carrying a $\mathbb{Z}$-module structure (automatic) that is finitely generated and free over $\mathbb{Z}$. Let $\iota$ be an index type and let $f : \iota \to \operatorname{End}_{\mathbb{Z}}(\Lambda)$ be a family of $\mathbb{Z}$-linear endomorphisms of $\Lambda$ which is linearly independent over $\mathbb{Z}$ in the $\mathbb{Z}$-module $\operatorname{End}_{\mathbb{Z}}(\Lambda)$, in the sense of `LinearIndependent`. The conclusion is that the family of base-changed endomorphisms $i \mapsto (f\,i)\otimes_{\mathbb{Z}} K$, each regarded as a $K$-linear endomorphism of $K \otimes_{\mathbb{Z}} \Lambda$ via `LinearMap.baseChange`, is linearly independent over $K$ in $\operatorname{End}_K(K \otimes_{\mathbb{Z}} \Lambda)$. Equivalently: if a finitely supported family $(c_i)$ of elements of $K$ satisfies $\sum_i c_i \,(f_i)_K = 0$, then all $c_i$ vanish. No finiteness is assumed on $\iota$.
--
--   This is the standard statement that linear independence of integral operators survives base change along the flat extension $\mathbb{Z} \to K$ for $K$ of characteristic zero. It is used in the construction of families of operators on a Tate module after tensoring with a characteristic-zero coefficient field, namely by [`ModularCurve.exists_tateModule_inertia_fixed_linearIndependent_heckeLatticeAlgebra_orbit`](thm.html#ModularCurve.exists_tateModule_inertia_fixed_linearIndependent_heckeLatticeAlgebra_orbit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearIndependent_linearMap_baseChange_of_int.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem LinearIndependent.linearMap_baseChange_of_int (K : Type) [Field K] [CharZero K]
    (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ] {ι : Type}
    (f : ι → Module.End ℤ Λ) (hf : LinearIndependent ℤ f) :
    LinearIndependent K (fun i => ((f i).baseChange K : Module.End K (K ⊗[ℤ] Λ))) := by sorry
