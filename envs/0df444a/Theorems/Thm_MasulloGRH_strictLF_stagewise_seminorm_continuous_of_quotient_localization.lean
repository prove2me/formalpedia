-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_stagewise_seminorm_continuous_of_quotient_localization
-- name    : MasulloGRH.strictLF_stagewise_seminorm_continuous_of_quotient_localization
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:15:07.564503+00:00
-- url     : https://prove2.me/theorems/d998b148-7c50-4912-bb2a-e6b73b63ecc0
-- title:
--   Localized control in an inductive-limit quotient implies continuity of stagewise continuous subspace seminorms
-- statement:
--   Let $E$ be a Hausdorff complex locally convex space exhausted by increasing linear subspaces $X_n$ with the induced topologies. Suppose $E$ carries their locally convex inductive limit topology. For a linear subspace $V$ put $q:E\to E/V$. Assume that for every $n$ there exist $m\ge n$ and a zero-neighborhood $U$ in $X_n$ such that for every zero-neighborhood $W$ in $X_m$ there is a zero-neighborhood $G$ in $E/V$ satisfying
--   $$q(U)\cap G\subseteq q(W).$$
--   Let $p$ be a complex seminorm on $V$. If $p$ is continuous on every $V\cap X_n$, then $p$ is continuous for the subspace topology on $V$ induced by $E$. This gives a direct route from localized quotient control to the limit-subspace topology.
-- source:
--   J. Wengenroth, Acyclic inductive spectra of Fréchet spaces, Studia Math. 120 (1996), Theorem 2.7 and Corollary 3.4, https://doi.org/10.4064/sm-120-3-247-258 . Direct seminorm argument for the localized hypothesis, without metrizability or nuclearity assumptions on the stages.

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open Topology
namespace MasulloGRH

theorem strictLF_stagewise_seminorm_continuous_of_quotient_localization (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsHLCS E) (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n)
    (htop : ‹TopologicalSpace E› = sInf {t | IsLocallyConvexTopology E t ∧
      ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E)
    (hloc : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ 𝓝 (0 : X n), ∀ W ∈ 𝓝 (0 : X m),
      ∃ G ∈ 𝓝 (0 : E ⧸ V), ∀ x ∈ U, Submodule.Quotient.mk (x : E) ∈ G →
        ∃ w ∈ W, ((x:E) - (w:E)) ∈ V)
    (p : Seminorm ℂ V)
    (hp : ∀ n, Continuous (p.comp (Submodule.inclusion (inf_le_left : V ⊓ X n ≤ V)))) :
    Continuous p := by sorry

end MasulloGRH
