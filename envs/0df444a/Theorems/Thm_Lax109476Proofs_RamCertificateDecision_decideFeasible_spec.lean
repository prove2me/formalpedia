-- Prove2me | Theorems.Thm_Lax109476Proofs_RamCertificateDecision_decideFeasible_spec
-- name    : Lax109476Proofs.RamCertificateDecision.decideFeasible_spec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:30:57.711805+00:00
-- url     : https://prove2.me/theorems/9006b6d2-3402-467a-a9bf-16717d96a9a6
-- title:
--   Execution of stored rational feasibility decisions
-- statement:
--   Let $F$ be an integer linear system with $r$ rows and $s$ columns. Let $S$ bound these dimensions and let $2^{2S}$ bound its coefficient magnitudes. The feasibility command uses word width $w$, a source array prefix and a disjoint target prefix. Assume the stated decision-width bound and that the source system is encoded correctly. Then the command preserves the source representation and source-data predicate, and writes a Boolean feasibility decision at the target:
--   $$\operatorname{decision}(F)=\operatorname{feasibleSystem}(F).$$
--   Its operational running time is at most the explicit decision-cost function of $S$. Array-prefix disjointness and all required word-range conditions are hypotheses. This result supplies the actual feasibility subroutine used when selecting optimality, infeasibility or unboundedness certificates.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamCertificateDecision.lean, theorem decideFeasible_spec

import Definitions.Def_EdgeSublinearMWIS_Main_NativeOperationalInterfaces

theorem Lax109476Proofs.RamCertificateDecision.decideFeasible_spec : ∀ (r s S w : ℕ) (F : Lax109476.LinearProgram.Program ℤ r s) (source target : String),
  2 ^ (2 * S) < 2 ^ w →
    r * s + r + s + 4 < 2 ^ w →
      Lax109476Proofs.RamStoredFeasibility.wordWidth (Lax109476Proofs.RamCertificateDecision.sizeBound r s S) ≤ w →
        (∀ (i : Fin r) (j : Fin s), (F.A i j).natAbs ≤ 2 ^ (2 * S)) →
          (∀ (i : Fin r), (F.b i).natAbs ≤ 2 ^ (2 * S)) →
            (∀ (j : Fin s), F.c j = 0) →
              Lax109476Proofs.RamCopy.Disjoint (source ++ "system.A") (target ++ "lp.A") →
                Lax109476Proofs.RamCopy.Disjoint (source ++ "system.b") (target ++ "lp.A") →
                  Lax109476Proofs.RamCopy.Disjoint (source ++ "system.b") (target ++ "lp.b") →
                    (∀ t ∈ Lax109476Proofs.RamCopy.suffixes,
                        source ++ ("system.A" ++ t) ∉
                          (Lax109476Proofs.RamCertificateDecision.decideFeasible source target).warrs) →
                      (∀ t ∈ Lax109476Proofs.RamCopy.suffixes,
                          source ++ ("system.b" ++ t) ∉
                            (Lax109476Proofs.RamCertificateDecision.decideFeasible source target).warrs) →
                        Lax808846Proofs.Reasoning.Spec (2 ^ w)
                          (Lax109476Proofs.RamCertificateDecision.Input F source target)
                          (Lax109476Proofs.RamCertificateDecision.decideFeasible source target)
                          (fun (x τ : Lax808846Proofs.Imp.Env) =>
                            Lax109476Proofs.RamEquationData.Data F
                                (Lax109476Proofs.RamCertificateDecision.prefixedView source τ) ∧
                              Lax808846Proofs.Imp.Cond.evalB (2 ^ w) Lax109476Proofs.RamBisectionCommit.condition τ =
                                Option.some
                                  (Lax109476Proofs.RationalFeasibilityDecision.feasible
                                    (Lax109476Proofs.IntegerEncoding.rationalProgram F)))
                          (Lax109476Proofs.RamCertificateDecision.instructionBound r s S) := by sorry
