-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_fst
-- name    : LanglandsTunnell.CubicInduction.exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_fst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/486dc6f6-22ac-5272-af97-6a5bbf0ca792
-- title:
--   Levi-central units act trivially on a deeply contracted Whittaker function
-- statement:
--   Let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$, so that $\mathbb{Q}_v$ denotes the completion of $\mathbb{Q}$ at $v$, and write $\mathrm{GL}_3(\mathbb{Q}_v)$ for `LocalGL3 v`. Let $W_0 : \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ be a function satisfying two conditions. First, $W_0$ transforms under the standard upper unipotent subgroup by the inverse of the local standard additive character $\psi_v$: for all $x, y, z \in \mathbb{Q}_v$ and all $g$, $W_0\bigl(u(x,y,z)\,g\bigr) = \psi_v^{-1}(x+y)\,W_0(g)$, where $u(x,y,z)$ is the unipotent matrix with rows $(1,x,z)$, $(0,1,y)$, $(0,0,1)$. Second, for a fixed $d \in \mathbb{N}$, $W_0$ is right invariant under the level-$d$ principal congruence subgroup: whenever $k$ lies in the subgroup of elements of $\mathrm{GL}_3(\mathbb{Q}_v)$ all of whose entries, and all of whose inverse's entries, have valuation $\le 1$, and all entries of $k - 1$ have valuation $\le \exp(-d)$, then $W_0(gk) = W_0(g)$ for every $g$. Let $C \subseteq \mathrm{GL}_3(\mathbb{Q}_v)$ be compact. The assertion is that there exists $N \in \mathbb{N}$ such that for every $X \in C$, every triple $a : \mathrm{Fin}\,3 \to \mathbb{Q}_v^\times$ of units with $\mathrm{v}(a_0/a_1) \le \exp(-N)$, and all units $s,t$ lying in `higherUnitsAt ℚ v d` — that is, of valuation $1$ and, unless $d = 0$, with $\mathrm{v}(s-1), \mathrm{v}(t-1) \le \exp(-d)$ — one has $$W_0\bigl(\mathrm{diag}(a_0,a_1,a_2)\,\mathrm{diag}(s,t,t)\,X\bigr) = W_0\bigl(\mathrm{diag}(a_0,a_1,a_2)\,X\bigr).$$
--
--   This is the generator-level form of the asymptotic (Jacquet-module) behaviour of a Whittaker function on $\mathrm{GL}_3(\mathbb{Q}_v)$ along the parabolic of type $(1,2)$: once the torus element contracts the first simple root far enough, the centre of the Levi, truncated at level $d$, acts trivially on $W_0$ uniformly over a compact set of right translates. It feeds the Rankin–Selberg finiteness statement [`LanglandsTunnell.RankinSelberg.forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist`](thm.html#LanglandsTunnell.RankinSelberg.forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist), where it is used to bound the torus support of deeply twisted local integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_fst.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal

theorem LanglandsTunnell.CubicInduction.exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_fst
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
      Valued.v (((a 0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) / ((a 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) ≤
        WithZero.exp (-(N : ℤ)) →
      ∀ s t : (v.adicCompletion ℚ)ˣ, s ∈ higherUnitsAt ℚ v d → t ∈ higherUnitsAt ℚ v d →
        W₀ (diagonal3 v a * diagonal3 v ![s, t, t] * X) = W₀ (diagonal3 v a * X) := by sorry
