-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_isCompact_forall_setIntegral_translate_ne_zero_of_cuspidal
-- name    : LanglandsTunnell.RankinSelberg.exists_isCompact_forall_setIntegral_translate_ne_zero_of_cuspidal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/2069d39c-c852-5f5a-a3f8-0ee9283ed74f
-- title:
--   Ω-averaged Whittaker coefficients are compactly supported modulo the centre
-- statement:
--   Fix a nonzero prime $p$ of the ring of integers of $\mathbb Q$, write $F = \mathbb Q_p$ for the completion of $\mathbb Q$ at $p$, let $\theta_0 : F^\times \to \mathbb C^\times$ be a group homomorphism, and let $N$ be a nonzero ideal of $\mathcal O_{\mathbb Q}$. Let $w_2 : \mathrm{GL}_2(F) \to \mathbb C$ be a function subject to: (i) $w_2(n(x)g) = \psi_p(x)\,w_2(g)$ for all $x \in F$ and $g$, where $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $\psi_p$ is the local additive character obtained by composing the standard adelic character of $\mathbb Q$ with the embedding of $F$ into the adeles at $p$; (ii) right invariance $w_2(gk) = w_2(g)$ for $k$ in the subgroup of $\mathrm{GL}_2(F)$ that maps, under the embedding of $\mathrm{GL}_2(F)$ into $\mathrm{GL}_2$ of the finite adeles at the place $p$, into the adelic level-one congruence subgroup of level $N$; (iii) $w_2 \neq 0$; (iv) irreducibility: every nonzero $w$ in the $\mathbb C$-span $V$ of the right translates $g \mapsto w_2(gh)$ has $w_2$ in the span of its own right translates; (v) admissibility: for every open subgroup $U$ there is a finite set $B$ of functions such that every $U$-right-invariant $w \in V$ lies in the span of $B$; (vi) central character: $w_2(z\cdot 1_2\, g) = \theta_0(z)\,w_2(g)$; and (vii) cuspidality: for each $v \in V$ there is $N_0 \in \mathbb Z$ with $v(\mathrm{diag}(y,1)) = 0$ whenever $y \in F^\times$ has valuation at most $\exp N_0$. Then, with $\mathrm{GL}_2(F)$ carrying its Borel $\sigma$-algebra, for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$, every open compact subgroup $\Omega$, every $g_0 \in \mathrm{GL}_2(F)$ and every $w \in V$, there exists a compact set $C \subseteq \mathrm{GL}_2(F)$ such that whenever $\int_{\Omega} w(g_0 k g)\, d\mu_2(k) \neq 0$ there is $z \in F^\times$ with $z \cdot 1_2 \cdot g \in C$.
--
--   This is the local statement that matrix coefficients of a cuspidal (supercuspidal) irreducible admissible generic representation of $\mathrm{GL}_2(\mathbb Q_p)$, realised on its $\psi$-Whittaker model, are compactly supported modulo the centre; the coefficient here is the one attached to the smooth functional $u \mapsto \int_\Omega u(g_0 k)\, d\mu_2(k)$. It feeds the local Rankin–Selberg and Godement zeta integrals at $p$ in the Langlands–Tunnell part of the development, where convergence and functional equations for the cuspidal local factors are established.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_isCompact_forall_setIntegral_translate_ne_zero_of_cuspidal.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction UnramifiedWhittaker
open NumberField.AdelicLevel (diagOne)
open scoped Classical

theorem LanglandsTunnell.RankinSelberg.exists_isCompact_forall_setIntegral_translate_ne_zero_of_cuspidal
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (hcusp : ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0)
    :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))), IsOpen (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) → IsCompact (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∀ (g₀ : GL (Fin 2) (p.adicCompletion ℚ)),
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∃ C : Set (GL (Fin 2) (p.adicCompletion ℚ)), IsCompact C ∧
          ∀ g : GL (Fin 2) (p.adicCompletion ℚ), (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (g₀ * k * g) ∂μ₂) ≠ 0 →
            ∃ z : (p.adicCompletion ℚ)ˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) z * g ∈ C := by sorry
