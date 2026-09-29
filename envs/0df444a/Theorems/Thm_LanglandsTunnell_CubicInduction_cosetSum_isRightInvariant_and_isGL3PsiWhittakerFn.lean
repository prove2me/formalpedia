-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_cosetSum_isRightInvariant_and_isGL3PsiWhittakerFn
-- name    : LanglandsTunnell.CubicInduction.cosetSum_isRightInvariant_and_isGL3PsiWhittakerFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/623b479d-5046-5451-929a-e35d9840a3d8
-- title:
--   Coset sums preserve right U-invariance and the Whittaker law
-- statement:
--   Let $v$ be a nonzero prime of the ring of integers of $\mathbb{Q}$ (an element of the height one spectrum of $\mathcal{O}_{\mathbb{Q}}$), let $\psi_v$ be an additive character of the completion $\mathbb{Q}_v$ with values in $\mathbb{C}$, let $U$ be a subgroup of $\mathrm{GL}_3(\mathbb{Q}_v)$, let $\mathrm{gen} \in \mathrm{GL}_3(\mathbb{Q}_v)$, let $(\mathrm{reps}_i)_{i \in \iota}$ be a family of elements of $\mathrm{GL}_3(\mathbb{Q}_v)$ indexed by a finite type, and let $W \colon \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ be any function; write $(\mathrm{cosetSum}\,\mathrm{reps}\,W)(g) = \sum_{i} W(g\cdot \mathrm{reps}_i)$. The theorem asserts a conjunction of two implications. First: if $(\mathrm{reps}_i)$ is a Hecke coset system for $(U,\mathrm{gen})$, meaning each $\mathrm{reps}_i$ lies in the set $U\cdot\{\mathrm{gen}\}\cdot U$, every element of that set has the same image as some $\mathrm{reps}_i$ in $\mathrm{GL}_3(\mathbb{Q}_v)/U$, and $i \mapsto \mathrm{reps}_i U$ is injective, and if $W(gu) = W(g)$ for all $g$ and all $u \in U$, then $\mathrm{cosetSum}\,\mathrm{reps}\,W$ satisfies the same right $U$-invariance. Second: if $W(n(x,y,z)\,g) = \psi_v(x+y)\,W(g)$ for all $x,y,z \in \mathbb{Q}_v$ and all $g$, where $n(x,y,z)$ is the upper unipotent matrix with entries $x$, $y$, $z$ in positions $(1,2)$, $(2,3)$, $(1,3)$, then $\mathrm{cosetSum}\,\mathrm{reps}\,W$ satisfies the same identity. No hypothesis relating $\mathrm{gen}$ to the second assertion is required: part two holds for an arbitrary finite family.
--
--   This records the two transformation laws stable under the Hecke operator attached to a double coset $U\,\mathrm{gen}\,U$ on functions on $\mathrm{GL}_3(\mathbb{Q}_v)$: right invariance under the level subgroup, and the $\psi_v$-Whittaker law for the upper unipotent subgroup. It is used in the construction of a local Whittaker function with prescribed spherical behaviour at places which are not bad, within the cubic-induction (Langlands–Tunnell) part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_cosetSum_isRightInvariant_and_isGL3PsiWhittakerFn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.cosetSum_isRightInvariant_and_isGL3PsiWhittakerFn
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (U : Subgroup (LocalGL3 v)) (gen : LocalGL3 v)
    {ι : Type} [Fintype ι] (reps : ι → LocalGL3 v) (W : LocalGL3 v → ℂ) :
    (HeckeIntegralSeam.IsHeckeCosetSystem U gen reps → IsRightInvariant U W → IsRightInvariant U (cosetSum reps W)) ∧
    (IsGL3PsiWhittakerFn ψv W → IsGL3PsiWhittakerFn ψv (cosetSum reps W)) := by sorry
