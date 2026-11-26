-- Prove2me | Theorems.Thm_IntConeFPT_lemma_5_merge_writer
-- name    : IntConeFPT.lemma_5_merge_writer
-- status  : Open
-- author  : @ohnesorgefelix
-- created : 2026-11-26T13:24:54.143925+00:00
-- url     : https://prove2.me/theorems/37307c74-a7e4-4fb7-a9b6-442d2cca6c36
-- title:
--   Lemma 5, merging step — a polynomial-time machine averaging generators with equal integer coordinates
-- statement:
--   There are an absolute constant $C$ and a deterministic algorithm with the following property. Its input consists of dimensions $d,k$ and an oracle output $(\varphi,(a,b),L)$, where $L=((x_i,u_i,\theta_i))_i$ is a list of generators $x_i\in\mathbb Z^d$, $u_i\in\mathbb Q^k$ with positive rational multiplicities $\theta_i>0$. The algorithm outputs $(\varphi,(a,b),\mathrm{fracMerge}(L))$. Here $\mathrm{fracMerge}(L)$ replaces all entries with the same integer coordinates $x$ by the single entry
--   $$\Bigl(x,\ \frac{\sum_{x_i=x}\theta_iu_i}{\sum_{x_i=x}\theta_i},\ \sum_{x_i=x}\theta_i\Bigr).$$
--   The output has length at most $\ell^C$, and the algorithm halts within $\ell^C$ steps, where $\ell$ is the input length.
--
--   This is the algorithmic content of the merging step at the end of the proof of Lemma 5 (p.36): "Since the averaging combines at most $d+k+1$ generators of polynomial encoding length, the resulting rational generators and multiplicities also have polynomial encoding length. The averaging takes polynomial time."
--
--   **Formalization Note.** The input is `encNat d ++ [3] ++ encNat k ++ [3] ++ encOracle o` and the output is `encOracle` of the merged tuple. Rationals are written in lowest terms, so the bound on the output length is part of the statement. The machine model is the mission's `Machine`/`RunsWithin`.
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint), proof of Lemma 5, Section B.1, pp.35–36 ("Combine generators with the same integer coordinates by averaging … The averaging takes polynomial time", p.36)

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
import Definitions.Def_IntConeFPT_Formulation
import Definitions.Def_IntConeFPT_fracMerge

open OnlineCRS.Combine

namespace IntConeFPT

theorem lemma_5_merge_writer :
    ∃ C : ℕ, ∃ M : Machine, ∀ (d k : ℕ)
      (o : ℚ × ((Fin d → ℚ) × (Fin k → ℚ)) × ℚ × List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ)),
        (∀ e ∈ o.2.2.2, 0 < e.2.2) →
        let inp := encNat d ++ [3] ++ encNat k ++ [3] ++ encOracle o
        let out := encOracle (o.1, o.2.1, o.2.2.1, fracMerge o.2.2.2)
        out.length ≤ inp.length ^ C ∧ RunsWithin M inp out ((inp.length : ℝ) ^ C) := by sorry

end IntConeFPT
