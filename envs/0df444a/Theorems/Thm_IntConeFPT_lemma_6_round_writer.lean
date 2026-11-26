-- Prove2me | Theorems.Thm_IntConeFPT_lemma_6_round_writer
-- name    : IntConeFPT.lemma_6_round_writer
-- status  : Open
-- author  : @ohnesorgefelix
-- created : 2026-11-26T09:12:24.900951+00:00
-- url     : https://prove2.me/theorems/b3eecc88-094d-47f1-9365-49514bc92be7
-- title:
--   Lemma 6 constructive congruence-preserving rounding and certificate deduplication
-- statement:
--   There exist an absolute constant $C \in \mathbb{N}$ and a deterministic TM2 machine $P$ over $\{0,1,2,3\}$ that, given framed context `ctx` encoding $(d, k, r, z, n)$ with $d \ge 1$, $n \ge 1$, and an encoded fractional representation $o = (\Phi, (a^\star, b^\star), \mathrm{rep})$ of length at most $2^d$, strictly positive weights, and weight sum $n$, computes in polynomial time $(|\text{ctx}| + |\text{encOracle}(o)| + 2^d + 2)^C$ the binary certificate encoding `encCert out` obtained by: (1) taking integer floors $q_e = \lfloor \theta_e \rfloor$, (2) partitioning $\lfloor 2^d \delta_e \rfloor$ copies of each support index into $\ell - 1$ groups of size $2^d$ averaged via $(r + \sum a_i, \frac{1}{2^d} \sum u_i)$, (3) forming the final residual element $(x_{\mathrm{final}}, u_{\mathrm{final}})$ when $\ell \ge 1$, and (4) merging entries sharing identical generator coordinates $(x, u)$.
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328, Lemma 6, pp. 9 and 37

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Machine
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem
import Definitions.Def_IntConeFPT_Residue

open OnlineCRS.Combine IntConeFPT

theorem IntConeFPT.lemma_6_round_writer :
    let frame := fun (x y : List Sym) => x.flatMap (fun s => [(0 : Sym), s]) ++ 1 :: y
    ∃ C : ℕ, ∃ P : Machine,
      ∀ (d k : ℕ), 1 ≤ d →
      ∀ (r : Residue d) (z : Fin d → ℤ) (n : ℕ), 1 ≤ n →
      ∀ (o : ℚ × ((Fin d → ℚ) × (Fin k → ℚ)) × ℚ × List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ)),
        o.2.2.2.length ≤ 2 ^ d →
        (∀ e ∈ o.2.2.2, 0 < e.2.2) →
        (o.2.2.2.map fun e => e.2.2).sum = (n : ℚ) →
        let rep := o.2.2.2
        let q := fun e : (Fin d → ℤ) × (Fin k → ℚ) × ℚ => ⌊e.2.2⌋₊
        let δ := fun e : (Fin d → ℤ) × (Fin k → ℚ) × ℚ => e.2.2 - (q e : ℚ)
        let ρ := fun e : (Fin d → ℤ) × (Fin k → ℚ) × ℚ => ⌊((2 ^ d : ℕ) : ℚ) * δ e⌋₊
        let ℓ := n - (rep.map q).sum
        let poolIdx := (List.finRange rep.length).flatMap fun idx => List.replicate (ρ (rep.get idx)) idx
        let usedIdx := poolIdx.take (2 ^ d * (ℓ - 1))
        let chunk := fun j : Fin (ℓ - 1) => (usedIdx.drop (j.1 * 2 ^ d)).take (2 ^ d)
        let xAvg := fun (j : Fin (ℓ - 1)) (i : Fin d) =>
          ((r i : ℕ) : ℤ) + ((chunk j).map fun idx => ((rep.get idx).1 i - ((r i : ℕ) : ℤ)) / (2 ^ d : ℤ)).sum
        let uAvg := fun (j : Fin (ℓ - 1)) (i : Fin k) =>
          ((chunk j).map fun idx => (rep.get idx).2.1 i).sum / ((2 ^ d : ℕ) : ℚ)
        let β := fun idx : Fin rep.length => δ (rep.get idx) - (usedIdx.count idx : ℚ) / ((2 ^ d : ℕ) : ℚ)
        let xFinal := fun i : Fin d =>
          z i - (rep.map fun e => (q e : ℤ) * e.1 i).sum - ((List.finRange (ℓ - 1)).map fun j => xAvg j i).sum
        let uFinal := fun i : Fin k =>
          ((List.finRange rep.length).map fun idx => β idx * (rep.get idx).2.1 i).sum
        let raw : List ((Fin d → ℤ) × (Fin k → ℚ) × ℕ) :=
          if ℓ = 0 then rep.map fun e => (e.1, e.2.1, q e)
          else (rep.filterMap fun e => if q e = 0 then none else some (e.1, e.2.1, q e)) ++
               ((List.finRange (ℓ - 1)).map fun j => (xAvg j, uAvg j, 1)) ++
               [(xFinal, uFinal, 1)]
        let out : List ((Fin d → ℤ) × (Fin k → ℚ) × ℕ) :=
          raw.foldr (fun e acc =>
            if acc.any (fun h => decide ((h.1, h.2.1) = (e.1, e.2.1))) then
              acc.map (fun h => if (h.1, h.2.1) = (e.1, e.2.1) then (h.1, h.2.1, h.2.2 + e.2.2) else h)
            else e :: acc) []
        let ctx := encNat d ++ [3] ++ encNat k ++ [3] ++ encResidue r ++ encIntVec z ++ encNat n ++ [3]
        RunsWithin P (frame ctx (encOracle o)) (encCert out)
          (((ctx.length : ℝ) + ((encOracle o).length : ℝ) + (2 ^ d : ℝ) + 2) ^ C) := by sorry
