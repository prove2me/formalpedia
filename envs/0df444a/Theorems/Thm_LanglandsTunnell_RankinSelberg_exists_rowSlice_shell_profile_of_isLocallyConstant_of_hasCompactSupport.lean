-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rowSlice_shell_profile_of_isLocallyConstant_of_hasCompactSupport
-- name    : LanglandsTunnell.RankinSelberg.exists_rowSlice_shell_profile_of_isLocallyConstant_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/af205475-172b-5cab-940b-806fdacc6403
-- title:
--   Shell profile of a unipotent row-slice integral over ℚₚ
-- statement:
--   Let $p$ be a height-one prime of $\mathcal O_{\mathbb Q}$, write $F = \mathbb Q_p$ for the completion at $p$ with valuation ring $\mathcal O$, and let $\varpi \in \mathcal O$ have nonzero image in $F$ (hypothesis `hπ`) and valuation $\exp(-1)$, i.e. $\varpi$ is a uniformiser. Let $\Phi : M_2(F) \to \mathbb C$ be locally constant with compact support. Equip $F$ with its Borel $\sigma$-algebra and let $\psi =$ `psiLocal` be the standard additive character of $F$ (the standard adelic character of $\mathbb Q$ composed with the embedding of $F$ as the component at $p$), and let $\mathrm{d}x$ be `selfDualHaarAt`, the additive Haar measure normalised so that $\mathcal O$ has mass $(\mathrm{N}\mathfrak p)^{-n/2}$, $n$ the level of $\psi$. Put $B(g) = \int_F \psi(x)\,\Phi(n(x)g)\,\mathrm{d}x$, where $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$. The conclusion is a threefold conjunction: (i) for every $g \in GL_2(F)$ the integrand $x \mapsto \psi(x)\Phi(n(x)g)$ is integrable; (ii) there is an open subgroup $U \le GL_2(F)$ with $B(gk) = B(g)$ for all $k \in U$ and all $g$; (iii) there are integers $c, M$ and a real $C$ such that for every $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178) (the pullback, under the embedding of $GL_2(F)$ into $GL_2$ of the finite adeles placing $g$ at $p$ and $1$ elsewhere, of the adelic level-one subgroup at the unit ideal), all $n_1, n_2 \in \mathbb Z$ and all units $u$ of $F$ with $|u| = 1$, setting $g = \mathrm{diag}(\varpi,\varpi)^{n_2}\,\mathrm{diag}(\varpi^{n_1}u, 1)\,k$, one has $B(g) = 0$ whenever $c < n_2$, or $n_2 < -M$, or $n_1 + n_2 < -M$; $B(g) = B\bigl(\mathrm{diag}(\varpi,\varpi)^{n_2}\,\mathrm{diag}(\varpi^{\,c-n_2}, 1)\,k\bigr)$ whenever $c \le n_1 + n_2$; and $\|B(g)\| \le C$ in all cases.
--
--   This is the local archimedean-free input to the Rankin–Selberg computation in the style of Jacquet–Langlands: the row-slice (partial Whittaker) integral of a locally constant compactly supported function on $M_2(\mathbb Q_p)$ is integrable, right-invariant under an open subgroup, supported in finitely many central shells along the diagonal torus, eventually constant in the remaining torus direction, and uniformly bounded. It feeds the local vanishing statement over the level-one subgroup, the Laurent expansion of the $GL_2$ Godement zeta integral along the torus, and the shell-gauge analysis of the rational torus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_rowSlice_shell_profile_of_isLocallyConstant_of_hasCompactSupport.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker
  LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.RankinSelberg.exists_rowSlice_shell_profile_of_isLocallyConstant_of_hasCompactSupport
    (p : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    letI := localBorel ℚ p

    (∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      Integrable (fun x : (p.adicCompletion ℚ) => NumberField.StandardAddChar.psiLocal ℚ p x *
        Φ ((unipotent x * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) (selfDualHaarAt ℚ p)) ∧

    (∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
        (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (g * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) =
        (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (g) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p))) ∧

    ∃ (c M : ℤ) (C : ℝ), ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ (n₁ n₂ : ℤ) (u : (p.adicCompletion ℚ)ˣ),
      Valued.v (u : (p.adicCompletion ℚ)) = 1 →

        (c < n₂ →
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) = 0) ∧

        (n₂ < -M →
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) = 0) ∧

        (n₁ + n₂ < -M →
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) = 0) ∧

        (c ≤ n₁ + n₂ →
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) =
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ (c - n₂) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p))) ∧

        (‖(∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p))‖ ≤ C) := by sorry
