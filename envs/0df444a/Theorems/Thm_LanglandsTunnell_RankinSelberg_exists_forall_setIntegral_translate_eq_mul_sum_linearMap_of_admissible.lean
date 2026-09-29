-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_translate_eq_mul_sum_linearMap_of_admissible
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_setIntegral_translate_eq_mul_sum_linearMap_of_admissible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/513b6f47-60f5-54e4-844f-891181fdb3c3
-- title:
--   Separation of variables for Ω-averages of local translates
-- statement:
--   Let $p$ be a height-one prime of the ring of integers $\mathcal{O}_{\mathbb Q}$, let $N$ be a non-zero ideal of $\mathcal{O}_{\mathbb Q}$, and set $G = \mathrm{GL}_2$ of the $p$-adic completion of $\mathbb Q$ at $p$. Let $w_{2\mathrm{base}} : G \to \mathbb C$ be a function invariant under right translation by every element of [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178), that is, by every $k \in G$ whose image under the local embedding into $\mathrm{GL}_2$ of the finite adele ring lies in the level-one congruence subgroup attached to $N$ (both $k$ and $k^{-1}$ having level-one matrix entries). Write $V \subseteq (G \to \mathbb C)$ for the $\mathbb C$-span of the right translates $g \mapsto w_{2\mathrm{base}}(gh)$, $h \in G$, and assume $V$ is admissible in the following sense: for every open subgroup $U \le G$ there is a finite set $B$ of functions $G \to \mathbb C$ such that every $w \in V$ invariant under right translation by all $k \in U$ lies in the span of $B$. Equip $G$ with its Borel $\sigma$-algebra. Then for every Haar measure $\nu$ on $G$, every open and compact subgroup $\Omega \le G$, and every $w \in V$, there exist $n \in \mathbb N$, functions $w_j : G \to \mathbb C$ and $\mathbb C$-linear functionals $\ell_j$ on the full space of functions $G \to \mathbb C$, indexed by $j \in \mathrm{Fin}\,n$, such that each $w_j$ lies in $V$ and is locally constant; each $\ell_j$ satisfies $\ell_j(g \mapsto v(gk)) = \ell_j(v)$ for all $k \in \Omega$ and all $v \in V$; each function $h \mapsto \ell_j(x \mapsto w(xh))$ is locally constant; and for all $g, h \in G$, $$\int_{\Omega} w(g\,\omega\,h)\,d\nu(\omega) = \nu(\Omega)\,\sum_{j} \ell_j\bigl(x \mapsto w(xh)\bigr)\, w_j(g),$$ the factor $\nu(\Omega)$ entering as the real number $\nu(\Omega)$ viewed in $\mathbb C$.
--
--   This is the separation-of-variables identity for averages over a compact open subgroup used in the local theory of Rankin–Selberg convolutions (Jacquet–Piatetski-Shapiro–Shalika, §6.3): the $w_j$ play the role of a basis of the $\Omega$-fixed vectors and the coefficients $\ell_j(\pi(h)w)$ of smooth matrix coefficients. It is invoked in the local analysis of Rankin–Selberg integrals of Whittaker functions, in particular in the non-vanishing and Kirillov-pairing statements for cuspidal data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_translate_eq_mul_sum_linearMap_of_admissible.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory

theorem LanglandsTunnell.RankinSelberg.exists_forall_setIntegral_translate_eq_mul_sum_linearMap_of_admissible
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
    ∀ (ν : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [ν.IsHaarMeasure]
      (Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))),
      IsOpen (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) → IsCompact (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∃ (n : ℕ) (wj : Fin n → GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
          (ℓ : Fin n → ((GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] ℂ)),
          (∀ j, wj j ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h))) ∧
          (∀ j, IsLocallyConstant (wj j)) ∧
          (∀ j, ∀ k ∈ Ω, ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ℓ j (fun g => v (g * k)) = ℓ j v) ∧
          (∀ j, IsLocallyConstant (fun h : GL (Fin 2) (p.adicCompletion ℚ) => ℓ j (fun x => w (x * h)))) ∧
          ∀ g h : GL (Fin 2) (p.adicCompletion ℚ),
            ∫ ω in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (g * ω * h) ∂ν =
              ((ν (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) * ∑ j, ℓ j (fun x => w (x * h)) * wj j g := by sorry
