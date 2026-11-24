-- Prove2me | Theorems.Thm_IntConeFPT_section_3_6_driver
-- name    : IntConeFPT.section_3_6_driver
-- status  : Open
-- author  : @ohnesorgefelix
-- created : 2026-11-24T11:16:43.148882+00:00
-- url     : https://prove2.me/theorems/77c486e1-e9bf-44df-b9a4-3bbd399f08a9
-- title:
--   §3.6 — Turing-machine orchestration for the two-call reduction of Theorem 1
-- statement:
--   Let $M_{\mathrm{box}}$ and $M_{\mathrm{cnt}}$ be deterministic multi-stack Turing machines over the alphabet $\{0,1,2,3\}$. There exist an exponent $C_{\mathrm{drv}} \in \mathbb{N}$ and a deterministic Turing machine $M_{\mathrm{main}}$ such that for every valid instance $I$ of (♣), every integer $M \ge 1$, every output $o_0$ for $I$ and $\widehat{o}$ for the homogenized instance $\widehat{I}$, and all nonnegative real step bounds $T_{\mathrm{box}}, T_0, T_{\mathrm{hom}} \ge 0$, setting $N_\star := N_\star(\tau, d, k, U(I, M))$:
--
--   if $M_{\mathrm{box}}$ halts on $\operatorname{enc}(I)$ with output $\operatorname{enc}(M)$ in at most $T_{\mathrm{box}}$ steps, $M_{\mathrm{cnt}}$ halts on $(\operatorname{enc}(I), \operatorname{enc}(N_\star))$ with output $\operatorname{enc}(o_0)$ in at most $T_0$ steps, and $M_{\mathrm{cnt}}$ halts on $(\operatorname{enc}(\widehat{I}), \operatorname{enc}(N_\star))$ with output $\operatorname{enc}(\widehat{o})$ in at most $T_{\mathrm{hom}}$ steps, then $M_{\mathrm{main}}$ halts on $\operatorname{enc}(I)$ with output $\operatorname{enc}(\operatorname{resolveOutput}(I, o_0, \widehat{o}))$ within
--
--   $$
--   \bigl(|I| + |\operatorname{enc}(M)| + |\operatorname{enc}(N_\star)| + T_{\mathrm{box}} + T_0 + T_{\mathrm{hom}} + 2\bigr)^{C_{\mathrm{drv}}}
--   $$
--
--   steps.
--
--   This lemma encapsulates the Turing-machine tape manipulation, arithmetic computation of $U(I, M)$ and $N_\star$, construction of the zero-right-hand-side instance $\widehat{I}$, two subroutine invocations of Proposition 14, and exact rational polynomial evaluation of the homogeneous certificate's cost in the proof of Theorem 1 (Section 3.6, p. 18).
--
--   **Formalization Note** Placing $C_{\mathrm{drv}}$ and $M_{\mathrm{main}}$ after $(M_{\mathrm{box}}, M_{\mathrm{cnt}})$ and before all inputs ensures $C_{\mathrm{drv}}$ is an absolute constant once the two subroutine machines from `(2.1)` and Proposition 14 are fixed, while allowing $C_{\mathrm{drv}}$ to absorb the per-step push factor of $M_{\mathrm{cnt}}$ when bounding the output certificate length.
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), §3.6, pp.17–18, eq. (3.4) and Proof of Theorem 1

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
import Definitions.Def_IntConeFPT_Homogenized

open OnlineCRS.Combine

namespace IntConeFPT

/-- **Section 3.6: Turing-machine orchestration for the two-call reduction of Theorem 1.**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), §3.6, Proof of Theorem 1, p.18: given a machine `M_box`
computing a box bound `M ≥ 1` on `I` and a machine `M_cnt` solving counted optimization (Proposition
14), a composite deterministic machine computes `U = coeffBoundU I M` and `N⋆`, runs `M_cnt` on
`(I, N⋆)` and on `(homInstance I, N⋆)`, tests whether the returned homogeneous representation has
negative rational cost, and outputs `resolveOutput I o₀ oHom` within polynomial overhead in the
input, `enc(N⋆)`, and subroutine step bounds. -/
theorem section_3_6_driver (M_box M_cnt : Machine) :
    ∃ C_drv : ℕ, ∃ M_main : Machine,
      ∀ (I : Instance), I.Valid →
      ∀ (M : ℕ), 1 ≤ M →
      ∀ (o₀ : Output I) (oHom : Output (homInstance I)) (T_box T₀ T_hom : ℝ),
        0 ≤ T_box → 0 ≤ T₀ → 0 ≤ T_hom →
        let N_star := Nstar I.τ I.d I.k (coeffBoundU I M)
        RunsWithin M_box (encInstance I) (encNat M) T_box →
        RunsWithin M_cnt (encInstance I ++ encNat N_star ++ [3]) (encOutput o₀) T₀ →
        RunsWithin M_cnt (encInstance (homInstance I) ++ encNat N_star ++ [3]) (encOutput oHom) T_hom →
        RunsWithin M_main (encInstance I) (encOutput (resolveOutput I o₀ oHom))
          (((encInstance I).length + (encNat M).length + (encNat N_star).length +
            T_box + T₀ + T_hom + 2 : ℝ) ^ C_drv) := by sorry

end IntConeFPT
