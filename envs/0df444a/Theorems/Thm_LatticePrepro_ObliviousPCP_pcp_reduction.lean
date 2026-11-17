-- Prove2me | Theorems.Thm_LatticePrepro_ObliviousPCP_pcp_reduction
-- name    : LatticePrepro.ObliviousPCP.pcp_reduction
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-16T22:10:47.724266+00:00
-- url     : https://prove2.me/theorems/167dbe3a-29fc-4960-a831-bc536aa62549
-- title:
--   Theorem 6.4 — reduction from query-oblivious PCPs to nearest codeword with preprocessing
-- statement:
--   Let a query-oblivious PCP with enumerable predicate families (Definition 6.1) be given, with alphabet $\Sigma$, $\mathsf R$ random bits, $\mathsf q\ge1$ queries and $\mathsf m$ accepting views, and let $L$ be a language for which it has perfect completeness and soundness error $\mathsf s>0$. Let $F$ be a field, let $\iota\colon F^{\mathsf m}\to F^{B}$ be an injective $F$-linear map such that every nonzero vector of the code $\iota(F^{\mathsf m})$ has Hamming weight at least $\delta\cdot B$, and let $\Gamma\ge0$ be an integer with
--   $$\Gamma<\delta\cdot\mathsf s^{-1/\mathsf q}.$$
--   Let $C$ and $y_x$ be the code and the targets of Construction 6.2, and let $Y=B\cdot2^{\mathsf R}\cdot\mathsf q$. Then:
--
--   1. **Completeness.** For every $x\in L$, $\Delta(y_x,C)\le Y$.
--   2. **Soundness.** For every $x\notin L$, $\Delta(y_x,C)>\Gamma\cdot Y$.
--   3. **Size.** The code has block length $M=(|\Sigma|+\Gamma)\cdot Y+1$.
--
--   The code $C$ depends only on the PCP, the encoding map and $\Gamma$, not on the instance. So the map $x\mapsto y_x$ sends the instances of $L$ to targets within distance $Y$ of the fixed code $C$, and all other instances to targets at distance more than $\Gamma\cdot Y$. This is the combinatorial content of the reduction from $L$ to $\Gamma$-gap nearest codeword with preprocessing over $F$.
--
--   **Formalization Note.** This is Theorem 6.4 without its running-time claims. The final sentence of the theorem, that the construction is a preprocessing reduction when the parameters are polynomial in the instance length, is therefore not formalized. The hypotheses are weaker than in the paper: $\mathsf s<1$ and $\Gamma\ge2$ are not assumed, $\delta$ is only a lower bound on the relative distance of the code $\iota(F^{\mathsf m})$, and $F$ need not be finite. Instances form an arbitrary type. The bound $\mathsf m\le2^{\mathsf R}\cdot\mathsf k\cdot|\Sigma|^{\mathsf q}$ from the proof is the separate theorem `card_views_le`. $\Delta(y,C)$ is `CodeFamily.codeDist`, and the exponent is a real power, `ε ^ (-(1 : ℝ) / q)`. The Lean names `ε`, `E`, `g`, `ρ`, `q` stand for $\mathsf s$, $\iota$, $\Gamma$, $\mathsf R$, $\mathsf q$.
-- source:
--   G. Fenzi, G. Weissenberg, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634), Theorem 6.4 (\label{thm:pcp-reduction}); Lean: LatticePrepro/PCP/Reduction.lean, LatticePrepro.ObliviousPCP.pcp_reduction

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_PCP_Verifier
import Definitions.Def_LatticePrepro_PCP_Code

open LatticePrepro
open LatticePrepro.ObliviousPCP
variable {X : Type} (P : ObliviousPCP X) {F : Type} [Field F] [DecidableEq F] {B : ℕ}

theorem LatticePrepro.ObliviousPCP.pcp_reduction {Lang : Set X} {ε δ : ℝ} (hc : P.PerfectlyComplete Lang)
    (hs : P.SoundnessError Lang ε) (hε : 0 < ε) {E : (P.Views → F) →ₗ[F] (Fin B → F)}
    (hE : Function.Injective E)
    (hδ : ∀ c ∈ LinearMap.range E, c ≠ 0 → δ * B ≤ hammingNorm c) {g : ℕ}
    (hg : (g : ℝ) < δ * ε ^ (-(1 : ℝ) / P.q)) :
    (∀ x ∈ Lang, CodeFamily.codeDist (P.target E g x) (P.code E g) ≤ P.radius B) ∧
    (∀ x, x ∉ Lang → g * P.radius B < CodeFamily.codeDist (P.target E g x) (P.code E g)) ∧
    Fintype.card (P.Coord B ⊕ Fin (g * P.radius B + 1)) =
      (Fintype.card P.Alphabet + g) * P.radius B + 1 := by sorry
