-- Prove2me | Theorems.Thm_InteractionElim_Main_lemma_B_2
-- name    : InteractionElim.Main.lemma_B_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:21:59.612888+00:00
-- url     : https://prove2.me/theorems/cffadc1d-c807-4ba6-8d68-67735fe25a5a
-- title:
--   Lemma B.2 — scripted-prefix probability comparison: $q_{x,s}\le\alpha_{s,j,a}(Ax)$ and $\delta\ge\alpha_{s,j,a}(Ay)\,\mathbb E_x[1\{\Gamma,S=s\}7^{-\sum N_i}]$
-- statement:
--   Work in the setting of §B.1: a workflow instance with $L\ge\ln(R+1)$ and $wL\ge\gamma/2$, and a fixed reliable admissible protocol. Fix $u=u_0$. For a successful paid-bit/ordered-marker signature $s$ (the list of paid bits and one completion marker per stage, submitted values omitted), a stage $j$ and a preceding truth $a$ (values on the blocks before $B_j$), let $\pi(s,j,a)$ be the public prefix of $s$ strictly before the complete stage-$j$ submission, with earlier submitted values $a$. There is a function $\alpha_{s,j,a}:\operatorname{im}A\to[0,1]$ such that, with $\Gamma$ full success and $q_{x,s}=\Pr_x(\Gamma,S=s)$: whenever $q_{x,s}>0$ and $x_{<j}=a$,
--   $$
--   q_{x,s}\le\alpha_{s,j,a}(Ax), \tag{B.10}
--   $$
--   and for every world $y$ with $y_{<j}=a$ and $y_{B_j}\ne x_{B_j}$,
--   $$
--   \delta\ge\alpha_{s,j,a}(Ay)\ \mathbb E_x\Big[1\{\Gamma,S=s\}\,7^{-\sum_{i\in B_j:\,x_i\ne y_i}N_i}\Big]. \tag{B.11}
--   $$
--   The function $\alpha_{s,j,a}$ depends only on the expert record and this prescribed public prefix, not on either realized private tape or the agent's unreported observations.
--
--   This likelihood comparison produces, from any randomized ongoing protocol, the certificates that the converse (Proposition B.3) charges.
--
--   **Formalization Note** $\alpha$ is a function of the record only (for the fixed protocol, $s$, $j$, $a$), so the last sentence holds by its type; its values matter on $\operatorname{im}A$, where they lie in $[0,1]$. $N_i$ are the call counts of the world-$x$ execution at success; the expectation is a lower Lebesgue integral.
--
--   Differences from the source:
--   - encoding: coordinates [R] = {1,…,R}, ordered blocks B_1,…,B_m, x ∈ F_2^R → `Fin R`, a surjective block map `Fin R → Fin m` (0-based stage order), vectors `Fin R → ZMod 2`; reason: index shift only; every ordered partition into nonempty blocks is such a surjection
--   - reading: §2 (p. 4) describes protocols in prose: a public parser, an expert whose bits depend only on Ax, the public history and its tape, an agent with private current-block queries that may preempt the expert by a submission, private abandonment, independent private tapes → `Protocol`/`step`/`run`: deterministic strategies of fair-coin tapes and views; the expert's abandonment is decided at every newly reached public history; an illegal move (query outside the current block, a paid bit out of turn, yielding when the expert is not designated) is abandonment; strategies are measurable in their tapes; reason: the source gives the model only in prose; this reading keeps every constraint of p. 4 (no shared tape, no free symbol, no clock), fair-coin tapes simulate any private randomization, and measurability is the standing convention that makes the execution law defined
--   - encoding: the fee (2.1) and the values C_ad, C_pre, C_lin as infima of fees → fees, C_ad, C_pre, C_lin in ℝ≥0∞ (lower integral of the path cost, supremum over worlds, infimum over the class); reason: (2.2)'s remark allows infinite-fee protocols; every finite value is the same real number
--   - generalization: the reliable admissible protocol in Appendix B's finite-fee reduction, with R ≥ 16, L ≥ ln(R+1) and wL ≥ γ/2 → L ≥ ln(R+1), wL ≥ γ/2, Reliable and Admissible, allowing also infinite expected fee; reason: every finite-fee source instance is included; the proof of (B.10)-(B.11) uses finite successful prefixes and nonnegative limits, not integrability of the total fee
--   - reading: 'If … q_{x,s} > 0, and a = x_{<j}, then (B.10). For every world y …, (B.11)' → both (B.10) and (B.11) assume q_{x,s} > 0 and x_{<j} = a; reason: (B.11) refers to the same x; when q_{x,s} = 0 its right side vanishes
--   - encoding: α_{s,j,a} : im A → [0,1], depending only on the expert record and the prefix → α : F_2^{rows} → ℝ with 0 ≤ α(Ax) ≤ 1 for every x, existentially quantified after the protocol, s, j, a; reason: values off im A are never used; a function of the record alone has the stated dependence by construction
--   - encoding: a successful signature s → any list s of bits and markers; reason: a signature that never occurs has q_{x,s} = 0 and the statement is vacuous for it
-- source:
--   Jin, Zang, Xu, Li, Eliminating Ongoing Interaction in Long-Running Verification Agents, STOC 2027 submission (manuscript sha256 44f6d829…), p. 24, Lemma B.2, Eqs. (B.10)-(B.11); standing assumptions p. 22, §B.1

import Mathlib
import Definitions.Def_InteractionElim_Main_Protocol

open scoped BigOperators ENNReal
open MeasureTheory Matrix

namespace InteractionElim.Main

theorem lemma_B_2 (I : Instance) (hL : Real.log ((I.R : ℝ) + 1) ≤ I.L)
    (hwL : (I.γ : ℝ) / 2 ≤ (I.w : ℝ) * I.L) (pr : Protocol I) (hrel : Reliable pr)
    (hadm : Admissible pr) (u0 : ZMod 2) (s : List (Option Bool))
    (j : Fin I.m) (a : Fin I.R → ZMod 2) :
    ∃ α : (Fin I.nrows → ZMod 2) → ℝ,
      (∀ x : Fin I.R → ZMod 2, 0 ≤ α (I.A *ᵥ x) ∧ α (I.A *ᵥ x) ≤ 1) ∧
      (∀ x : Fin I.R → ZMod 2, (∀ i, I.block i < j → x i = a i) →
        0 < law I {ω | SucceedsWith pr x u0 ω s} →
        law I {ω | SucceedsWith pr x u0 ω s} ≤ ENNReal.ofReal (α (I.A *ᵥ x))) ∧
      (∀ x y : Fin I.R → ZMod 2, (∀ i, I.block i < j → x i = a i) →
        0 < law I {ω | SucceedsWith pr x u0 ω s} →
        (∀ i, I.block i < j → y i = a i) → (∃ i, I.block i = j ∧ y i ≠ x i) →
        ENNReal.ofReal (α (I.A *ᵥ y)) *
            ∫⁻ ω, (⨆ t, if (run pr x u0 ω t).status = .success ∧
                  signature (run pr x u0 ω t).hist = s then
                (7⁻¹ : ℝ≥0∞) ^ (∑ i ∈ Finset.univ.filter (fun i => I.block i = j ∧ x i ≠ y i),
                  (run pr x u0 ω t).calls i)
                else 0) ∂(law I) ≤
          ENNReal.ofReal (I.δ : ℝ)) := by sorry

end InteractionElim.Main
