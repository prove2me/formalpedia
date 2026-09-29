-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_mem_gl3CyclicSubspace_twist_det
-- name    : LanglandsTunnell.CubicInduction.mem_gl3CyclicSubspace_twist_det
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/2243ebf9-cdbd-5060-b234-553c5840988c
-- title:
--   Twisting by χᵥ∘det preserves the cyclic subspace
-- statement:
--   Let $v$ be a point of the height-one spectrum of the ring of integers of $\mathbb{Q}$, let $\chi_v$ be a monoid homomorphism from the units of the $v$-adic completion of $\mathbb{Q}$ to $\mathbb{C}^\times$, and let $W$ be a complex-valued function on `LocalGL3 v`, the group $\mathrm{GL}_3$ over that completion. Write $W^{\chi}(x) = \chi_v(\det x)\,W(x)$, and let `gl3CyclicSubspace W` denote the $\mathbb{C}$-submodule of all functions on $\mathrm{GL}_3$ spanned by the right translates $x \mapsto W(xh)$, $h \in \mathrm{GL}_3$. The conclusion is a conjunction of four assertions: (i) for every $W'$ in the cyclic subspace of $W$, the twist $(W')^{\chi}$ lies in the cyclic subspace of $W^{\chi}$; (ii) conversely, every $W''$ in the cyclic subspace of $W^{\chi}$ is of the form $(W')^{\chi}$ for some $W'$ in the cyclic subspace of $W$; (iii) $W^{\chi} = 0$ if and only if $W = 0$; and (iv) for every subgroup $U$ of $\mathrm{GL}_3$ on which $\chi_v \circ \det$ is identically $1$, and every function $W'$ with $W'(gk) = W'(g)$ for all $k \in U$ and all $g$, the twist $(W')^{\chi}$ satisfies the same right $U$-invariance. Together (i) and (ii) say that the cyclic subspace of $W^{\chi}$ is exactly the set of twists of members of the cyclic subspace of $W$.
--
--   This records the compatibility of twisting a function on $\mathrm{GL}_3(\mathbb{Q}_v)$ by a character of the determinant with the formation of the cyclic space of right translates, together with the preservation of right invariance under a subgroup in the kernel of $\chi_v \circ \det$. It is used in the construction of the twisted local models attached to a cubic induction, in particular by [`LanglandsTunnell.CubicInduction.isCubicInductionDataOn_twist_det`](thm.html#LanglandsTunnell.CubicInduction.isCubicInductionDataOn_twist_det) and by the local zeta-integral statements for twisted cubic induction forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_mem_gl3CyclicSubspace_twist_det.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.mem_gl3CyclicSubspace_twist_det
    (v : HeightOneSpectrum (𝓞 ℚ)) (χv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (W : LocalGL3 v → ℂ) :
    (∀ W' ∈ gl3CyclicSubspace W,
        (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W' x) ∈ gl3CyclicSubspace (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x)) ∧
    (∀ W'' ∈ gl3CyclicSubspace (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x),
        ∃ W' ∈ gl3CyclicSubspace W, W'' = (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W' x)) ∧
    ((fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x) = 0 ↔ W = 0) ∧
    (∀ U : Subgroup (LocalGL3 v), (∀ k ∈ U, χv (Matrix.GeneralLinearGroup.det k) = 1) →
      ∀ W' : LocalGL3 v → ℂ, (∀ k ∈ U, ∀ g : LocalGL3 v, W' (g * k) = W' g) →
        ∀ k ∈ U, ∀ g : LocalGL3 v, (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W' x) (g * k) = (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W' x) g) := by sorry
