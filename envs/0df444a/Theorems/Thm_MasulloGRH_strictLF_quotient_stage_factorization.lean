-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_quotient_stage_factorization
-- name    : MasulloGRH.strictLF_quotient_stage_factorization
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T22:48:54.77561+00:00
-- url     : https://prove2.me/theorems/5ce07934-6818-4d79-8284-cb4df6fd84e0
-- title:
--   Factorization of the steps of a strict LF quotient through quotients of the original steps
-- statement:
--   Let $E=\bigcup_k E_k$ be a strict locally convex inductive limit of an increasing sequence of nuclear Fréchet spaces $E_k$ (each carrying the topology induced by $E$), and let $F\subset E$ be a closed subspace. Suppose that the quotient $Q=E/F$, with the quotient topology, is itself a strict locally convex inductive limit of an increasing sequence of nuclear Fréchet subspaces $Q_n$ (each carrying the topology induced by $Q$).
--
--   For each $k$ let $P_k=E_k/(F\cap E_k)$ with the quotient topology of $E_k$, and let $r_k\colon P_k\to Q$ be the injective linear map induced by the inclusion $E_k\hookrightarrow E$, i.e. $r_k(x+F\cap E_k)=x+F$.
--
--   Then for every $n$ there exist an index $k$ and a continuous linear map $v\colon Q_n\to P_k$ with
--   $$r_k\circ v=\iota_n,$$
--   where $\iota_n\colon Q_n\hookrightarrow Q$ is the inclusion; that is, $Q_n\subset r_k(P_k)$ and the factor $r_k^{-1}|_{Q_n}\colon Q_n\to P_k$ is continuous.
--
--   Proof idea: $Q_n$ is a Fréchet space, $Q$ is Hausdorff, every $P_k$ is a Fréchet space mapped continuously and injectively into $Q$, and $Q_n\subset Q=\bigcup_k r_k(P_k)$. Grothendieck's factorization theorem (Baire category plus the open mapping theorem applied to the closed graphs $\{(y,z)\in Q_n\times P_k : y=r_k z\}$) yields the required $k$ and $v$.
--
--   **Formalization Note** $P_k$ is `X k ⧸ V.comap (X k).subtype` and $r_k$ is `Submodule.mapQ _ V (X k).subtype le_rfl`. Nuclearity of the steps is included to match the setting of the corollary; it is not needed for the factorization.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, Corollary C.1.5.13, proof, pp. 668–669. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf (factorization step); this is an instance of Grothendieck's factorization theorem, cf. Meise–Vogt, Introduction to Functional Analysis, §24 (Grothendieck factorization theorem).

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_quotient_stage_factorization (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (Y : ℕ → Submodule ℂ (E ⧸ V)) (hYmono : Monotone Y)
    (hYexh : ∀ y : E ⧸ V, ∃ n, y ∈ Y n) (hY : ∀ n, IsFrechet (Y n) ∧ IsNuclear (Y n))
    (hYtop : (inferInstance : TopologicalSpace (E ⧸ V)) =
      sInf {t | IsLocallyConvexTopology (E ⧸ V) t ∧
        ∀ n, @Continuous (Y n) (E ⧸ V) _ t Subtype.val})
    (n : ℕ) :
    ∃ (k : ℕ) (v : Y n →L[ℂ] (X k ⧸ V.comap (X k).subtype)),
      ∀ y : Y n, Submodule.mapQ (V.comap (X k).subtype) V (X k).subtype le_rfl (v y) = (y : E ⧸ V) := by sorry

end MasulloGRH
