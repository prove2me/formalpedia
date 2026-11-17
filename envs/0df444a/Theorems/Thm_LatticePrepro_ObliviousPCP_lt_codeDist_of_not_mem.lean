-- Prove2me | Theorems.Thm_LatticePrepro_ObliviousPCP_lt_codeDist_of_not_mem
-- name    : LatticePrepro.ObliviousPCP.lt_codeDist_of_not_mem
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-16T22:10:45.834939+00:00
-- url     : https://prove2.me/theorems/da8cfdcb-9b06-4dcc-8545-c0ab441b34b2
-- title:
--   Theorem 6.4 (soundness) — $\Delta(y_x,C)>\Gamma\cdot Y$ for instances outside the language
-- statement:
--   Consider Construction 6.2 for a query-oblivious PCP with enumerable predicate families (Definition 6.1) with $\mathsf R$ random bits, $\mathsf q\ge1$ queries and $\mathsf m$ accepting views, a field $F$, an $F$-linear map $\iota\colon F^{\mathsf m}\to F^{B}$ and an integer $\Gamma\ge0$. Let $C$ be its code, $y_x$ its targets, and $Y=B\cdot2^{\mathsf R}\cdot\mathsf q$. Suppose that
--
--   - the PCP has soundness error $\mathsf s>0$ for a language $L$: for every instance $x\notin L$, every proof is accepted for at most $\mathsf s\cdot2^{\mathsf R}$ random strings;
--   - $\iota$ is injective, and every nonzero vector of the code $\iota(F^{\mathsf m})$ has Hamming weight at least $\delta\cdot B$, for a real number $\delta$;
--   - $\Gamma<\delta\cdot\mathsf s^{-1/\mathsf q}$, which is condition (28).
--
--   Then for every instance $x\notin L$,
--   $$\Delta(y_x,C)>\Gamma\cdot Y .$$
--
--   This is the soundness part of Theorem 6.4. If $G_0v=b_x$ has no solution, then $y_x=(0^{M_0},1^{H})$ and every codeword vanishes on the last $H=\Gamma\cdot Y+1$ coordinates. Otherwise, by (30), the distance from $y_x$ to $C$ is the least weight of $G_1v$ over the solutions $v$ of $G_0v=b_x$, and every solution has weight more than $\Gamma\cdot Y$.
--
--   **Formalization Note.** The hypotheses are weaker than in the paper: $\mathsf s<1$ and $\Gamma\ge2$ are not assumed, $\delta$ is only a lower bound on the relative distance of the code $\iota(F^{\mathsf m})$, and $F$ need not be finite. $\Delta(y,C)$ is `CodeFamily.codeDist`, the minimum Hamming distance from $y$ to a codeword. The Lean names `ε`, `E`, `g`, `ρ`, `q` stand for $\mathsf s$, $\iota$, $\Gamma$, $\mathsf R$, $\mathsf q$.
-- source:
--   G. Fenzi, G. Weissenberg, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634), Theorem 6.4 (\label{thm:pcp-reduction}), soundness, with (30) (\label{eq:pcp-target-distance}); Lean: LatticePrepro/PCP/Reduction.lean, LatticePrepro.ObliviousPCP.lt_codeDist_of_not_mem

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_PCP_Verifier
import Definitions.Def_LatticePrepro_PCP_Code

open LatticePrepro
open LatticePrepro.ObliviousPCP
variable {X : Type} (P : ObliviousPCP X) {F : Type} [Field F] [DecidableEq F] {B : ℕ}

theorem LatticePrepro.ObliviousPCP.lt_codeDist_of_not_mem {Lang : Set X} {ε δ : ℝ} (hs : P.SoundnessError Lang ε)
    (hε : 0 < ε) {E : (P.Views → F) →ₗ[F] (Fin B → F)} (hE : Function.Injective E)
    (hδ : ∀ c ∈ LinearMap.range E, c ≠ 0 → δ * B ≤ hammingNorm c) {g : ℕ}
    (hg : (g : ℝ) < δ * ε ^ (-(1 : ℝ) / P.q)) {x : X} (hx : x ∉ Lang) :
    g * P.radius B < CodeFamily.codeDist (P.target E g x) (P.code E g) := by sorry
