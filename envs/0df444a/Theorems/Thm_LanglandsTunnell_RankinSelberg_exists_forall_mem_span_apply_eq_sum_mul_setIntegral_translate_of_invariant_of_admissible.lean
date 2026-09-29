-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_mem_span_apply_eq_sum_mul_setIntegral_translate_of_invariant_of_admissible
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_mem_span_apply_eq_sum_mul_setIntegral_translate_of_invariant_of_admissible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/e422b2df-4d19-5e0f-a79c-e5662a1541ad
-- title:
--   Ω-averaged evaluations represent invariant functionals on admissible translate spaces
-- statement:
--   Fix a finite place $p$ of $\mathbb{Q}$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$) and a non-zero ideal $N$ of $\mathcal{O}_{\mathbb{Q}}$, and write $G = \mathrm{GL}_2(\mathbb{Q}_p)$ for the general linear group over the completion `p.adicCompletion ℚ`. Let $w_2 : G \to \mathbb{C}$ be a function which is invariant under right translation by every element of [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N`](def/AdelicDock_LocalEmbedding.html#L178), that is, by the subgroup of $G$ consisting of those $g$ whose image under the local embedding into $\mathrm{GL}_2$ of the finite adèles lies in the level-one subgroup `AdelicLevel.finiteLevelOne` attached to $N$ (both $g$ and $g^{-1}$ having level-one matrix entries for $N$). Let $V \subseteq (G \to \mathbb{C})$ be the $\mathbb{C}$-span of the right translates $g \mapsto w_2(gh)$, $h \in G$. Assume $V$ is admissible in the following sense: for every open subgroup $U \le G$ there is a finite set $B$ of functions $G \to \mathbb{C}$ such that every $w \in V$ invariant under right translation by all $k \in U$ lies in the span of $B$. Then, with $G$ carrying its Borel measurable structure, for every Haar measure $\mu_2$ on $G$, every subgroup $\Omega \le G$ which is open and compact as a subset, and every $\mathbb{C}$-linear functional $\ell$ on the full space of functions $G \to \mathbb{C}$ satisfying $\ell(g \mapsto v(gk)) = \ell(v)$ for all $k \in \Omega$ and all $v \in V$, there exist $n \in \mathbb{N}$, elements $g_1,\dots,g_n \in G$ and scalars $a_1,\dots,a_n \in \mathbb{C}$ such that $\ell(v) = \sum_{i=1}^n a_i \int_{\Omega} v(g_i k)\, d\mu_2(k)$ for every $v \in V$.
--
--   This is the local coefficient-span lemma used in the comparison of Godement–Jacquet and Rankin–Selberg local zeta integrals: an $\Omega$-invariant functional on the space of right translates of a level-one vector is a finite combination of $\Omega$-averaged, left-translated point evaluations, so that zeta integrals of smooth matrix coefficients reduce to those of the generating function itself. It is invoked in the statements about integrability, Laurent expansions and the cleared functional equation of the second Godement zeta coefficient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_mem_span_apply_eq_sum_mul_setIntegral_translate_of_invariant_of_admissible.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory

theorem LanglandsTunnell.RankinSelberg.exists_forall_mem_span_apply_eq_sum_mul_setIntegral_translate_of_invariant_of_admissible
    (p : HeightOneSpectrum (𝓞 ℚ))
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))),
      IsOpen (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) → IsCompact (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∀ (ℓ : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] ℂ),
        (∀ k ∈ Ω, ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ℓ (fun g => v (g * k)) = ℓ v) →
        ∃ (n : ℕ) (g : Fin n → GL (Fin 2) (p.adicCompletion ℚ)) (a : Fin n → ℂ),
          ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
            ℓ v = ∑ i, a i * ∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), v (g i * k) ∂μ₂ := by sorry
