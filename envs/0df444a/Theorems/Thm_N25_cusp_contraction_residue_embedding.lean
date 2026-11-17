-- Prove2me | Theorems.Thm_N25_cusp_contraction_residue_embedding
-- name    : N25.cusp_contraction_residue_embedding
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:31:40.926054+00:00
-- url     : https://prove2.me/theorems/c004b7f2-2f61-4823-a6db-a84531dadd1c
-- title:
--   Contraction embeds residue fields compatibly
-- statement:
--   Let $Q$ be a rational place and $P$ a geometric place whose valuation ring contracts to that of $Q$. There exists an injective ring homomorphism $\rho:k(Q)\to k(P)$ between the residue fields such that for every $a\in\mathcal O_Q$,
--
--   $$\rho(\overline a)=\overline{\iota(a)},$$
--
--    where $\iota:F_{\mathbb Q}\hookrightarrow F_{\overline{\mathbb Q}}$ is the constant-field embedding. This transports residue-field roots of unity from a geometric lift to the rational closed point.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_Endgame

set_option autoImplicit false
open N25
open N25.Endgame AlgebraicCurve

theorem N25.cusp_contraction_residue_embedding (Q : QPlace) (P : GPlace)
    (hQ : Q.toValuationSubring = P.toValuationSubring.comap emb25.toRingHom) :
    ∃ ρ : Q.ResidueField →+* P.ResidueField,
      Function.Injective ρ ∧
      ∀ a : Q.toValuationSubring,
        ρ (IsLocalRing.residue _ a) =
          IsLocalRing.residue P.toValuationSubring
            ⟨emb25 a, by
              exact (congrArg (fun S : ValuationSubring FQ => (a : FQ) ∈ S) hQ).mp a.property⟩ := by sorry
