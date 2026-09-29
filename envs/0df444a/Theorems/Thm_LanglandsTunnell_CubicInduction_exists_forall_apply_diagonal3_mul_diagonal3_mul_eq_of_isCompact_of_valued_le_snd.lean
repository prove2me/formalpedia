-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd
-- name    : LanglandsTunnell.CubicInduction.exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/a1eb6ca1-bca0-5580-9ceb-e6e7fc75e00f
-- title:
--   Deep central units diag(t,t,s) act trivially on contracted Whittaker values
-- statement:
--   Let $v$ be a nonzero prime of the ring of integers of $\mathbb{Q}$, with completion $\mathbb{Q}_v$, and let $W_0 : \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ satisfy the Whittaker transformation law for the inverse $\psi^{-1}$ of the standard local additive character `psiLocal` at $v$: for all $x,y,z \in \mathbb{Q}_v$ and all $g$, $W_0(u(x,y,z)\,g) = \psi^{-1}(x+y)\,W_0(g)$, where $u(x,y,z)$ is the upper unipotent matrix with entries $x,y$ above the diagonal and $z$ in the corner. Let $d \in \mathbb{N}$ and assume $W_0$ is right invariant under the level-$d$ congruence subgroup: $W_0(gk) = W_0(g)$ for every $g$ and every $k$ such that all entries of $k$ and of $k^{-1}$ have valuation $\le 1$ and all entries of $k - 1$ have valuation $\le q^{-d}$ (written `WithZero.exp (-(d:ℤ))`). Let $C \subseteq \mathrm{GL}_3(\mathbb{Q}_v)$ be compact. Then there is $N \in \mathbb{N}$ such that for every $X \in C$, every triple of units $a : \mathrm{Fin}\,3 \to \mathbb{Q}_v^{\times}$ with $|a_1/a_2| \le q^{-N}$ (indices $0,1,2$), and all units $s,t$ of valuation $1$ with $d = 0$ or $|s-1|, |t-1| \le q^{-d}$, one has $W_0\bigl(\mathrm{diag}(a)\,\mathrm{diag}(t,t,s)\,X\bigr) = W_0\bigl(\mathrm{diag}(a)\,X\bigr)$.
--
--   This is the stabilisation half of the Jacquet-module asymptotics of a Whittaker function along the parabolic of type $(2,1)$: once the last simple root is contracted far enough, units of the centre of the Levi that are congruent to $1$ modulo $v^d$ no longer change the value of a level-$d$ Whittaker function, uniformly over a compact set of right translates. It is used in the Rankin–Selberg part of the construction, in the analysis of twists of cyclic subspaces by characters of the diagonal torus at deep level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal

theorem LanglandsTunnell.CubicInduction.exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd
    (v : HeightOneSpectrum (𝓞 ℚ))

    (W₀ : LocalGL3 v → ℂ)
    (hW₀law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W₀)
    (d : ℕ)
    (hW₀lev : ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
      (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
          (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
      ∀ g : LocalGL3 v, W₀ (g * k) = W₀ g)

    (C : Set (LocalGL3 v)) (hC : IsCompact C) :
    ∃ N : ℕ, ∀ X ∈ C, ∀ a : Fin 3 → (v.adicCompletion ℚ)ˣ,
      Valued.v (((a 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) / ((a 2 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) ≤
        WithZero.exp (-(N : ℤ)) →
      ∀ s t : (v.adicCompletion ℚ)ˣ, s ∈ higherUnitsAt ℚ v d → t ∈ higherUnitsAt ℚ v d →
        W₀ (diagonal3 v a * diagonal3 v ![t, t, s] * X) = W₀ (diagonal3 v a * X) := by sorry
