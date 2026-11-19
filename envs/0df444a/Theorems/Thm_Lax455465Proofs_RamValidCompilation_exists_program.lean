-- Prove2me | Theorems.Thm_Lax455465Proofs_RamValidCompilation_exists_program
-- name    : Lax455465Proofs.RamValidCompilation.exists_program
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T09:16:54.874434+00:00
-- url     : https://prove2.me/theorems/48e5e019-746d-4498-8919-af14f4274dd4
-- title:
--   A compiled polynomial-time program for valid flow-cut instances
-- statement:
--   There are one fixed RAM program $p$ and polynomial width and time bounds $W,T$. Every valid rational product-demand instance $I$ with at least two positive-demand vertices has one certificate $\mathcal K$ such that
--   $$\operatorname{IsValid}(\text{kind},I,512,\mathcal K),$$
--   and $p$ returns its encoding in at most $T(\operatorname{bitSize}(I))$ steps at every host width at least $W(\operatorname{bitSize}(I))$. Undirected inputs carry the symmetry promise.
-- source:
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamValidCompilation.lean, theorem exists_program

import Definitions.Def_EdgeSublinearMWIS_Main_NativeSchemeInterfaces

theorem Lax455465Proofs.RamValidCompilation.exists_program : ∃ (p : Lax808846.Ram.Program) (WB : Polynomial ℕ) (TB : Polynomial ℕ),
  ∀ {n : ℕ} (kind : Lax455465.ProductNetwork.EdgeKind) (I : Lax455465.RationalEncoding.RationalInstance n),
    (kind = Lax455465.ProductNetwork.EdgeKind.undirected → I.network.IsUndirected) →
      2 ≤ Lax455465.ProductNetwork.supportCount I.weights →
        ∃ (certificate : Lax455465.FlowCutCertificate.Certificate n),
          Lax455465.FlowCutCertificate.IsValid kind I 512 certificate ∧
            ∀ (W : ℕ),
              Polynomial.eval (Lax759944.BinaryWordEncoding.bitSize (Lax455465.RationalEncoding.encodeInput kind I))
                    WB ≤
                  W →
                ∃
                  t ≤
                    Polynomial.eval
                      (Lax759944.BinaryWordEncoding.bitSize (Lax455465.RationalEncoding.encodeInput kind I)) TB,
                  Lax808846.Ram.RunsTo W p
                    ((Lax455465.RationalEncoding.encodeInput kind I).length ::
                      Lax455465.RationalEncoding.encodeInput kind I)
                    (Lax455465.FlowCutCertificate.encodeCertificate certificate) t := by sorry
