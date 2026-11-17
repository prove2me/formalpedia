-- Prove2me | Theorems.Thm_LatticePrepro_ObliviousPCP_lt_hammingNorm_stackMap_of_solution
-- name    : LatticePrepro.ObliviousPCP.lt_hammingNorm_stackMap_of_solution
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-16T22:11:08.031903+00:00
-- url     : https://prove2.me/theorems/68e30296-4f78-42cb-883c-310d55839da6
-- title:
--   Theorem 6.4 (soundness, main step) — every solution of $G_0v=b_x$ has weight more than $\Gamma\cdot Y$
-- statement:
--   Consider Construction 6.2 for a query-oblivious PCP with enumerable predicate families (Definition 6.1) with $\mathsf R$ random bits, $\mathsf q\ge1$ queries and $\mathsf m$ accepting views, a field $F$, an $F$-linear map $\iota\colon F^{\mathsf m}\to F^{B}$ and an integer $\Gamma\ge0$. Let $C$ be its code, $y_x$ its targets, and $Y=B\cdot2^{\mathsf R}\cdot\mathsf q$. Suppose that
--
--   - the PCP has soundness error $\mathsf s>0$ for a language $L$: for every instance $x\notin L$, every proof is accepted for at most $\mathsf s\cdot2^{\mathsf R}$ random strings;
--   - $\iota$ is injective, and every nonzero vector of the code $\iota(F^{\mathsf m})$ has Hamming weight at least $\delta\cdot B$, for a real number $\delta$;
--   - $\Gamma<\delta\cdot\mathsf s^{-1/\mathsf q}$, which is condition (28).
--
--   Then for every instance $x\notin L$ and every solution $v\in F^{\mathsf m}$ of $G_0v=b_x$, the Hamming weight $W(v)$ of $G_1v$ satisfies
--   $$W(v)>\Gamma\cdot Y .$$
--
--   This is the main step of the soundness proof of Theorem 6.4. A solution $v$ defines the lists $\Lambda_u=\{a\in\Sigma:v^{u,a}\ne0\}$. By the constraints (27), for every random string $r$ some accepting view $(V_{x,r},\mathbf a^{(r)})$ has a nonzero coefficient, and all its answers lie in the lists. A proof whose entries are independent and uniform in the lists is accepted for $r$ with probability at least $\prod_j|\Lambda_{u_{r,j}}|^{-1}$, so soundness gives (31), and the average list size is at least $\mathsf s^{-1/\mathsf q}$. By (29) every symbol of a list $\Lambda_u$ contributes weight at least $\delta\cdot B$ in each copy of the block of $u$, which gives $W(v)\ge\delta\cdot Y\cdot\mathsf s^{-1/\mathsf q}>\Gamma\cdot Y$.
--
--   **Formalization Note.** The random proof is replaced by a count over all proofs with entries in the lists. The hypotheses are weaker than in the paper: $\mathsf s<1$ and $\Gamma\ge2$ are not assumed, $\delta$ is only a lower bound on the relative distance of the code $\iota(F^{\mathsf m})$, and $F$ need not be finite. The exponent is a real power, `ε ^ (-(1 : ℝ) / q)`. The Lean names `ε`, `E`, `g`, `ρ`, `q` stand for $\mathsf s$, $\iota$, $\Gamma$, $\mathsf R$, $\mathsf q$.
-- source:
--   G. Fenzi, G. Weissenberg, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634), proof of Theorem 6.4 (\label{thm:pcp-reduction}), soundness, with (28) (\label{eq:pcp-gap}), (29) (\label{eq:pcp-weight}) and (31) (\label{eq:pcp-list-bound}); Lean: LatticePrepro/PCP/Reduction.lean, LatticePrepro.ObliviousPCP.lt_hammingNorm_stackMap_of_solution

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_PCP_Verifier
import Definitions.Def_LatticePrepro_PCP_Code

open LatticePrepro
open LatticePrepro.ObliviousPCP
variable {X : Type} (P : ObliviousPCP X) {F : Type} [Field F] [DecidableEq F] {B : ℕ}

theorem LatticePrepro.ObliviousPCP.lt_hammingNorm_stackMap_of_solution {Lang : Set X} {ε δ : ℝ}
    (hs : P.SoundnessError Lang ε) (hε : 0 < ε) {E : (P.Views → F) →ₗ[F] (Fin B → F)}
    (hE : Function.Injective E)
    (hδ : ∀ c ∈ LinearMap.range E, c ≠ 0 → δ * B ≤ hammingNorm c) {g : ℕ}
    (hg : (g : ℝ) < δ * ε ^ (-(1 : ℝ) / P.q)) {x : X} (hx : x ∉ Lang) {v : P.Views → F}
    (hv : P.constraintMap F v = P.constraintRhs F x) :
    g * P.radius B < hammingNorm (P.stackMap E v) := by sorry
