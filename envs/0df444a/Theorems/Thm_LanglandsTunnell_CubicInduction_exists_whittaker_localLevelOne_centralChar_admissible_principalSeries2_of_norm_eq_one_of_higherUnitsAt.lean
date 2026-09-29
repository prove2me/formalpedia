-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_of_norm_eq_one_of_higherUnitsAt
-- name    : LanglandsTunnell.CubicInduction.exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_of_norm_eq_one_of_higherUnitsAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/0d7d78e8-5f34-5e8e-b833-a3cde468e267
-- title:
--   Whittaker model of a unitary principal series of GL₂(ℚₚ)
-- statement:
--   Fix a height-one prime $p$ of $\mathcal{O}_{\mathbb{Q}}$, and a pair $\theta=(\theta_0,\theta_1)$ of group homomorphisms $(\mathbb{Q}_p^\times)\to\mathbb{C}^\times$ (writing $\mathbb{Q}_p$ for `p.adicCompletion ℚ`) with $\|\theta_i(z)\|=1$ for all $z$, together with exponents $c_0,c_1\in\mathbb{N}$ such that $\theta_i$ is trivial on `higherUnitsAt ℚ p (c i)`, the set of units $u$ with $v(u)=1$ and, when $c_i>0$, $v(u-1)\le\exp(-c_i)$. Let $N$ be a non-zero ideal and $b\in\mathbb{N}$ with $p^b\mid N$ and $p^{b+1}\nmid N$, and assume $c_0+c_1\le b$; let $\varpi$ lie in the valuation ring with non-zero image in $\mathbb{Q}_p$ and valuation $\exp(-1)$. Then there is a function $w:\mathrm{GL}_2(\mathbb{Q}_p)\to\mathbb{C}$ with the following properties, where $V$ denotes the $\mathbb{C}$-span of the right translates $g\mapsto w(gh)$. (1) $w\!\left(\begin{pmatrix}1&x\\0&1\end{pmatrix}g\right)=\psi_p(x)\,w(g)$, with $\psi_p$ the local component at $p$ of the standard additive character of the adeles of $\mathbb{Q}$. (2) $w(gk)=w(g)$ for $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N`](def/AdelicDock_LocalEmbedding.html#L178), the preimage in $\mathrm{GL}_2(\mathbb{Q}_p)$, under the embedding placing a matrix at $p$, of the subgroup of $\mathrm{GL}_2$ of the finite adeles whose elements and inverses satisfy the `IsLevelOneMatrix` condition for $N$. (3) $w\neq0$. (4) Every non-zero $w'\in V$ has $w$ in the span of its own right translates (irreducibility of $V$). (5) For every open subgroup $U$ there is a finite set $B$ of functions such that every right $U$-invariant element of $V$ lies in the span of $B$ (admissibility). (6) $w(zI\cdot g)=\theta_0(z)\theta_1(z)w(g)$ for $z\in\mathbb{Q}_p^\times$. (7) There is a $\mathbb{C}$-linear endomorphism $\Phi$ of the space of $\mathbb{C}$-valued functions on $\mathrm{GL}_2(\mathbb{Q}_p)$ that commutes with right translation on $V$, is injective on $V$, and maps $V$ into `principalSeries2 p θ`, the space of locally constant $f$ with $f(n(x)g)=f(g)$ and $f(\mathrm{diag}(a_0,a_1)g)=\theta_0(a_0)\theta_1(a_1)\sqrt{\|a_0\|/\|a_1\|}\,f(g)$. (8) There are reals $C,A$ with $\|w(\mathrm{diag}(\varpi^m,1)k)\|\le C\,(\mathrm{Nm}\,p)^{Am}$ for all integers $m\ge0$ and all $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178).
--
--   This is the existence of a Whittaker model for the unitary principal series $I(\theta_0,\theta_1)$ of $\mathrm{GL}_2(\mathbb{Q}_p)$, packaged with the level-$N$ invariance, irreducibility, admissibility, central character, principal-series embedding and polynomial growth in the form required by the local Rankin–Selberg computations. It is used by the variant of the statement that additionally records non-vanishing of the Whittaker function at the identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_of_norm_eq_one_of_higherUnitsAt.lean

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

theorem LanglandsTunnell.CubicInduction.exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_of_norm_eq_one_of_higherUnitsAt
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
