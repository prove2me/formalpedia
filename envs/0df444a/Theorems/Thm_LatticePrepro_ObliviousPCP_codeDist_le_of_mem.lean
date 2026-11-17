-- Prove2me | Theorems.Thm_LatticePrepro_ObliviousPCP_codeDist_le_of_mem
-- name    : LatticePrepro.ObliviousPCP.codeDist_le_of_mem
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-16T22:10:34.205859+00:00
-- url     : https://prove2.me/theorems/31306adf-902d-44d7-a4c3-789a45d6eed7
-- title:
--   Theorem 6.4 (completeness) — $\Delta(y_x,C)\le Y$ for instances in the language
-- statement:
--   Consider Construction 6.2 for a query-oblivious PCP with enumerable predicate families (Definition 6.1) with $\mathsf R$ random bits, $\mathsf q$ queries and $\mathsf m$ accepting views, a field $F$, an $F$-linear map $\iota\colon F^{\mathsf m}\to F^{B}$ and an integer $\Gamma\ge0$. Let $C$ be its code, $y_x$ its targets, and $Y=B\cdot2^{\mathsf R}\cdot\mathsf q$. Suppose that the PCP has perfect completeness for a language $L$: every $x\in L$ has a proof that is accepted for every random string. Then for every $x\in L$,
--   $$\Delta(y_x,C)\le Y .$$
--
--   This is the completeness part of Theorem 6.4. Take a proof $\pi$ that is accepted for every random string, and let $v$ be the indicator vector of the accepting views $(V_{x,r},\pi|_{I_r})$. Then $v$ satisfies the constraints (27), so $G_0v=b_x$ is solvable and $(G_1v_x,0^H)-(G_1v,0^H)$ is a codeword. The restrictions $v^{u,a}$ vanish for $a\ne\pi(u)$, so by the weight formula (29) the vector $G_1v$ has weight at most $B\cdot2^{\mathsf R}\cdot\mathsf q=Y$.
--
--   **Formalization Note.** This part needs no hypothesis on $\iota$, on $\Gamma$ or on the soundness of the PCP. $\Delta(y,C)$ is `CodeFamily.codeDist`, the minimum Hamming distance from $y$ to a codeword. The Lean names `ε`, `E`, `g`, `ρ`, `q` stand for $\mathsf s$, $\iota$, $\Gamma$, $\mathsf R$, $\mathsf q$.
-- source:
--   G. Fenzi, G. Weissenberg, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634), Theorem 6.4 (\label{thm:pcp-reduction}), completeness; Lean: LatticePrepro/PCP/Reduction.lean, LatticePrepro.ObliviousPCP.codeDist_le_of_mem

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_PCP_Verifier
import Definitions.Def_LatticePrepro_PCP_Code

open LatticePrepro
open LatticePrepro.ObliviousPCP
variable {X : Type} (P : ObliviousPCP X) {F : Type} [Field F] [DecidableEq F] {B : ℕ}

theorem LatticePrepro.ObliviousPCP.codeDist_le_of_mem {Lang : Set X} (hc : P.PerfectlyComplete Lang)
    (E : (P.Views → F) →ₗ[F] (Fin B → F)) (g : ℕ) {x : X} (hx : x ∈ Lang) :
    CodeFamily.codeDist (P.target E g x) (P.code E g) ≤ P.radius B := by sorry
