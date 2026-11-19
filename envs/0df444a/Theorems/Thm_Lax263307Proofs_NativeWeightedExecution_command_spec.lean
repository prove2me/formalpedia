-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeWeightedExecution_command_spec
-- name    : Lax263307Proofs.NativeWeightedExecution.command_spec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T09:17:09.49536+00:00
-- url     : https://prove2.me/theorems/ab82eef6-3647-413e-9fbf-107eef0cc55a
-- title:
--   Actual bounded execution of the native weighted approximation command
-- statement:
--   For a fixed implementation of a hereditary separator class, every member $G$, rational weight vector $w$ and rational $0<\varepsilon<1$ has an independent-set approximation $I$ for which the actual weighted command terminates within its declared instruction bound:
--   $$w(I)\ge(1-\varepsilon)\alpha_w(G).$$
--   The execution starts from the encoded weighted input, produces the encoded membership output, and obeys the explicit workspace and word-width bounds.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeWeightedExecution.lean, theorem command_spec; Bonnet–Chang, source PDF Section 6, pp.19–20

import Definitions.Def_EdgeSublinearMWIS_Main_NativeSchemeInterfaces

theorem Lax263307Proofs.NativeWeightedExecution.command_spec : ∀ {C : Lax263307.GraphClasses.GraphClass} (i : Lax263307Proofs.NativeQptasImplementation.Fixed C) {n : ℕ}
  (G : SimpleGraph (Fin n)) [inst : DecidableRel G.Adj],
  G ∈ C n →
    ∀ (weights : Fin n → ℚ) (ε : ℚ),
      0 < ε →
        ε < 1 →
          ∃ (I : Finset (Fin n)) (ext : String → ℕ),
            Lax263307.WeightedIndependentSet.IsApproximation G weights ε I ∧
              Lax808846Proofs.Reasoning.Spec (2 ^ Lax263307Proofs.NativeQptasWordBounds.width i weights ε)
                (fun (σ : Lax808846Proofs.Imp.Env) =>
                  σ = Lax808846Proofs.Imp.initEnv ext (Lax263307.IndependentSetEncoding.encodeInput G weights ε))
                (Lax263307Proofs.NativeWeightedExecution.command i)
                (fun (x τ : Lax808846Proofs.Imp.Env) => τ.out = Lax263307.IndependentSetEncoding.encodeOutput I)
                (Lax263307Proofs.NativeWeightedExecution.cost i weights ε) := by sorry
