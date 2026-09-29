-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_linearMap_principalSeries2_of_jacquet_ne_top
-- name    : LanglandsTunnell.CubicInduction.exists_linearMap_principalSeries2_of_jacquet_ne_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/0fc70910-6ba1-505e-b80c-1a965358bf26
-- title:
--   Principal series embedding when the Jacquet module is non-zero
-- statement:
--   Fix a non-zero prime $p$ of $\mathcal O_{\mathbb Q}$ and a non-zero ideal $N$ of $\mathcal O_{\mathbb Q}$, and let $w_{2\mathrm{base}} : \mathrm{GL}_2(\mathbb Q_p) \to \mathbb C$ be a function with the following properties: it satisfies the Whittaker transformation law $w_{2\mathrm{base}}(n(x)g) = \psi_p(x)\, w_{2\mathrm{base}}(g)$ for all $x \in \mathbb Q_p$, where $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $\psi_p$ is the component at $p$ of the standard additive character of the adèles of $\mathbb Q$; it is invariant under right translation by the subgroup [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178), the preimage in $\mathrm{GL}_2(\mathbb Q_p)$, under the embedding placing a local matrix at $p$, of the finite-adelic level-one subgroup attached to $N$; it is non-zero; and, writing $V$ for the $\mathbb C$-span of its right translates $g \mapsto w_{2\mathrm{base}}(gh)$, every non-zero $w \in V$ has $w_{2\mathrm{base}}$ in the span of its own right translates (irreducibility of $V$). Assume further that some $W \in V$ lies outside the span of the functions $g \mapsto W'(g\,n(t)) - W'(g)$ with $W' \in V$ and $t \in \mathbb Q_p$, i.e. the Jacquet module of $V$ is non-zero. Then there are characters $\chi_0, \chi_1 : \mathbb Q_p^\times \to \mathbb C^\times$, natural numbers $c_0, c_1$, and a $\mathbb C$-linear endomorphism $\Phi$ of the space of all $\mathbb C$-valued functions on $\mathrm{GL}_2(\mathbb Q_p)$ such that each $\chi_i$ is trivial on `higherUnitsAt` at level $c_i$ (the units $u$ of valuation $1$ with, when $c_i \neq 0$, $v(u-1) \le \exp(-c_i)$), $\Phi$ commutes with right translation on $V$, $\Phi$ is injective on $V$, and $\Phi(V)$ lies in `principalSeries2` for $\chi$, i.e. consists of locally constant functions $f$ with $f(n(x)g) = f(g)$ and $f(\mathrm{diag}(a_0,a_1)g) = \chi_0(a_0)\chi_1(a_1)\,\sqrt{\lVert a_0\rVert/\lVert a_1\rVert}\, f(g)$.
--
--   This is the local statement that an irreducible generic representation of $\mathrm{GL}_2(\mathbb Q_p)$ whose Jacquet module with respect to the upper unipotent radical is non-zero embeds, equivariantly for right translation, into a normalised principal series with quasi-characters of bounded conductor; the hypothesis on the Jacquet module excludes the supercuspidal case. It is used in the Rankin–Selberg part of the converse-theorem input, in the derivation of the cleared functional equation for the Godement zeta integrals attached to Whittaker functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_linearMap_principalSeries2_of_jacquet_ne_top.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

theorem LanglandsTunnell.CubicInduction.exists_linearMap_principalSeries2_of_jacquet_ne_top
    (p : HeightOneSpectrum (𝓞 ℚ))
    (N : Ideal (𝓞 ℚ)) (_hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hJ : ∃ W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      W ∉ Submodule.span ℂ {D : GL (Fin 2) (p.adicCompletion ℚ) → ℂ | ∃ W' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∃ t : p.adicCompletion ℚ, D = fun g : GL (Fin 2) (p.adicCompletion ℚ) => W' (g * unipotent t) - W' g}) :
    ∃ (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (c : Fin 2 → ℕ)
      (Φ : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)),
      (∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (c i), χ i u = 1) ∧
      (∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
        Φ (fun g => w (g * h)) = fun g => Φ w (g * h)) ∧
      (∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), Φ w = 0 → w = 0) ∧
      (∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), Φ w ∈ principalSeries2 p χ) := by sorry
