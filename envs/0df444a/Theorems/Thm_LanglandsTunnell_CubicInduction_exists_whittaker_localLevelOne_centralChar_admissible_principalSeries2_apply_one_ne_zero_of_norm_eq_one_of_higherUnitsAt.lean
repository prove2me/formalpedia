-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_apply_one_ne_zero_of_norm_eq_one_of_higherUnitsAt
-- name    : LanglandsTunnell.CubicInduction.exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_apply_one_ne_zero_of_norm_eq_one_of_higherUnitsAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/d5894c1e-ff23-5973-ba6b-da2f72163c0f
-- title:
--   Essential Whittaker vector at p with non-vanishing value at 1
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$, and let $\theta_0,\theta_1$ be monoid homomorphisms from the units of the completion $\mathbb{Q}_p$ to $\mathbb{C}^\times$, all of whose values have absolute value $1$ (hypothesis `hθu`). Let $c_0,c_1$ be natural numbers such that $\theta_i$ is trivial on `higherUnitsAt ℚ p (c i)`, the set of units $u$ with $v(u)=1$ and, when $c_i\neq 0$, $v(u-1)\le\exp(-c_i)$. Let $N\neq\bot$ be an ideal, $b$ a natural number with $p^b\mid N$ and $p^{b+1}\nmid N$, and assume $c_0+c_1\le b$. Let $\varpi$ lie in the valuation ring of $\mathbb{Q}_p$ with non-zero image $\pi$ of valuation $\exp(-1)$. Then there is a function $w:\mathrm{GL}_2(\mathbb{Q}_p)\to\mathbb{C}$ such that: $w\bigl(\binom{1\ x}{0\ 1}g\bigr)=\psi_p(x)w(g)$ for the local component $\psi_p$ at $p$ of the standard adelic additive character; $w(gk)=w(g)$ for all $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along the local embedding into $\mathrm{GL}_2$ of the finite adeles of the group of matrices which, together with their inverses, are level-one modulo $N$; $w\neq 0$ and $w(1)\neq 0$; writing $V$ for the $\mathbb{C}$-span of the right translates $g\mapsto w(gh)$, every non-zero $w'\in V$ has $w$ in the span of its own right translates (irreducibility of $V$); for every open subgroup $U$ of $\mathrm{GL}_2(\mathbb{Q}_p)$ there is a finite set $B$ of functions whose span contains every $U$-right-invariant element of $V$ (admissibility); $w(zI\cdot g)=\theta_0(z)\theta_1(z)\,w(g)$ for scalar matrices; there is a $\mathbb{C}$-linear endomorphism $\Phi$ of the space of functions on $\mathrm{GL}_2(\mathbb{Q}_p)$ which commutes with right translation on $V$, is injective on $V$, and carries $V$ into `principalSeries2 p θ`, the space of locally constant $f$ with $f\bigl(\binom{1\ x}{0\ 1}g\bigr)=f(g)$ and $f(\mathrm{diag}(a_0,a_1)g)=\theta_0(a_0)\theta_1(a_1)\sqrt{\|a_0\|/\|a_1\|}\,f(g)$; and there are reals $C,A$ with $\|w(\mathrm{diag}(\pi^m,1)k)\|\le C\,(\mathrm{absNorm}\,p)^{Am}$ for all integers $m\ge 0$ and all $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178).
--
--   This is the local input at $p$ of Casselman's essential (new) vector in the Whittaker model of the unitary principal series attached to $(\theta_0,\theta_1)$: it packages the Whittaker transformation law, invariance under the level-$N$ group at $p$, irreducibility and admissibility of the span of right translates, the central character, an equivariant injection into the normalised principal series, and moderate growth along the torus shells, together with the normalisation $w(1)\neq 0$. It feeds the local Rankin–Selberg integral computations used in the construction of the global forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_apply_one_ne_zero_of_norm_eq_one_of_higherUnitsAt.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

theorem LanglandsTunnell.CubicInduction.exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_apply_one_ne_zero_of_norm_eq_one_of_higherUnitsAt
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hθu : ∀ (i : Fin 2) (z : (p.adicCompletion ℚ)ˣ), ‖((θ i z : ℂˣ) : ℂ)‖ = 1)
    (c : Fin 2 → ℕ)
    (hcθ : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (c i), θ i u = 1)
    (N : Ideal (𝓞 ℚ)) (_hN : N ≠ ⊥) (b : ℕ)
    (hNb : p.asIdeal ^ b ∣ N ∧ ¬ p.asIdeal ^ (b + 1) ∣ N)
    (hcb : c 0 + c 1 ≤ b)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (_hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    ∃ w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ,
      (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g) ∧
      (∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) ∧
      w ≠ 0 ∧
      w 1 ≠ 0 ∧
      (∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)),
        w' ≠ 0 → w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w' (g * h))) ∧
      (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
        ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
          ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)),
            (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w' (g * k) = w' g) →
              w' ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
      (∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ 0 z * θ 1 z : ℂˣ) : ℂ) * w g) ∧
      (∃ Φ : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        (∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)), ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
          Φ (fun g => w' (g * h)) = fun g => Φ w' (g * h)) ∧
        (∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)), Φ w' = 0 → w' = 0) ∧
        (∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)), Φ w' ∈ principalSeries2 p θ)) ∧
      (∃ (C A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
        ‖w (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤
          C * (Ideal.absNorm p.asIdeal : ℝ) ^ (A * m)) := by sorry
