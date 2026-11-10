-- Prove2me | Theorems.Thm_InteractionElim_Main_lemma_C_1
-- name    : InteractionElim.Main.lemma_C_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:24:03.668622+00:00
-- url     : https://prove2.me/theorems/b2eca1ab-e924-4ad5-88a4-798b73a0ca82
-- title:
--   Lemma C.1 — certificate-weighted sequential verifier: accept w.p. $\ge9/10$ at $z$, $\le e^{-H}$ elsewhere, $O(tH+\ln(2+tH))$ expected calls, $O(tH\ln(2+tH))$ calls on every path
-- statement:
--   Let $D\subseteq\{0,1\}^r$ be a known cell with at least two elements and fix $z\in D$. Suppose $0\le a_i\le1$ satisfies $\sum_{i:\,z_i\ne y_i}a_i\ge1$ for every $y\in D\setminus\{z\}$, and put $t=\sum_ia_i$. Then $1\le t\le r$, and capping certificate entries at one preserves feasibility. Coordinate $i$ has independent BSC responses with known parameter $p_i\in[1/8,3/8]$. There is a universal constant $C$ such that for every integer $H\ge1$ a verification procedure using fresh private randomness and observations has the following properties:
--
--   1. at truth $z$ it accepts $z$ with probability at least $9/10$;
--   2. at every truth $x\in D\setminus\{z\}$ it accepts $z$ with probability at most $e^{-H}$;
--   3. at every truth $x\in D$ its expected number of calls is at most $C\{tH+\ln(2+tH)\}$, and its number of calls on every path is at most $CtH\ln(2+tH)$.
--
--   For rational $a_i,p_i$ the procedure uses rational computation and no real-number oracle. Its program halts on every private tape and finite response log; nontermination cannot count as rejection. The same holds for a finite binary linear-query menu whose actions return fresh, conditionally independent BSC responses with known parameters in $[1/8,3/8]$, the certificate constraints then being indexed by the actions that distinguish $z$ from $y$.
--
--   The statement is formalized for an arbitrary finite menu $(\ell_k,p_k)_{k<M}$ (coordinates are $\ell_i=e_i$, $M=r$): (i) capping at one preserves menu certificates; (ii) $1\le t\le M$; (iii) a measurable procedure with properties 1–3 exists; (iv) one program of the bit-cost machine computes such a procedure from the explicit rational data $(r,M,\ell,p,D,z,a,H)$.
--
--   This verifier decodes a uniformly inexpensive teaching cell at a cost proportional to the proposed root's certificate, with a deterministic call cap.
--
--   Differences from the source:
--   - encoding: universal constants, O(·) and ≍ → explicit existentially quantified positive real constants, quantified before every instance-dependent object; reason: the notation convention of p. 4: a ≍ b means two inequalities with positive universal constants
--   - generalization: coordinate queries with BSC responses, certificate constraints indexed by coordinates z_i ≠ y_i (the menu version is asserted in the lemma's last two sentences) → a finite menu of binary linear functionals ℓ_k with parameters p_k, constraints indexed by actions with ℓ_k·z ≠ ℓ_k·y; reason: the coordinate statement is the menu ℓ_i = e_i, M = r, and the lemma itself asserts the menu version
--   - reading: 'Thus 1 ≤ t ≤ r' → 1 ≤ t ≤ M (the menu size; M = r for coordinates); reason: the bound t ≤ r comes from a_i ≤ 1 over r coordinates
--   - reading: 'a verification procedure using fresh private randomness and observations' → a measurable `Procedure` (fair-coin tape and the response log ↦ next query or accept/reject) run under the product law of its tape and the per-action noise arrays; reason: the procedure model of Appendix C
--   - reading: 'The guarantee holds conditionally on any previous record that fixed z, a, H before these fresh observations. All calls are actual paid calls.' → no separate conjunct; reason: the procedure is a function of (D, z, a, p, H) and of its own fresh tape and noise, so conditioning on an earlier record fixing them leaves its law unchanged; every query is counted
--   - reading: 'For rational a_i, p_i, the procedure uses rational likelihood comparisons and no real-number oracle' → one program of the bit-cost machine which, for all rational data, halts on every tape and response log and computes a procedure with properties 1-3; reason: the finite rational operations and bounded fair-bit sampling on pp. 35-36 require an actually halting program, not the nonhalting default in procOfProgram; inconsistent logs can be rejected after finite replay
-- source:
--   Jin, Zang, Xu, Li, Eliminating Ongoing Interaction in Long-Running Verification Agents, STOC 2027 submission (manuscript sha256 44f6d829…), pp. 34-35, Lemma C.1, Eq. (C.1)

import Mathlib
import Definitions.Def_InteractionElim_Main_Procedure

open scoped BigOperators ENNReal
open MeasureTheory Matrix

namespace InteractionElim.Main

theorem lemma_C_1 :
    (∀ (r M : ℕ) (ell : Fin M → Fin r → ZMod 2) (D : Set (Fin r → ZMod 2))
        (z : Fin r → ZMod 2) (a : Fin M → ℝ),
      IsMenuCertificate ell D z a → IsMenuCertificate ell D z (fun k => min (a k) 1)) ∧
    (∀ (r M : ℕ) (ell : Fin M → Fin r → ZMod 2) (D : Finset (Fin r → ZMod 2))
        (z : Fin r → ZMod 2) (a : Fin M → ℝ),
      2 ≤ D.card → z ∈ D → (∀ k, a k ≤ 1) → IsMenuCertificate ell (D : Set _) z a →
        1 ≤ ∑ k, a k ∧ ∑ k, a k ≤ M) ∧
    ∃ C : ℝ, 0 < C ∧
      (∀ (r M : ℕ) (ell : Fin M → Fin r → ZMod 2) (p : Fin M → ℝ)
          (D : Finset (Fin r → ZMod 2)) (z : Fin r → ZMod 2) (a : Fin M → ℝ) (H : ℕ),
        2 ≤ D.card → z ∈ D → (∀ k, a k ≤ 1) → IsMenuCertificate ell (D : Set _) z a →
        (∀ k, 1 / 8 ≤ p k ∧ p k ≤ 3 / 8) → 1 ≤ H →
        ∃ pc : Procedure M Bool, pc.IsMeasurable ∧ VerifierSpec ell p D z (∑ k, a k) H C pc) ∧
      ∃ prog : Program,
        ∀ (r M : ℕ) (ell : Fin M → Fin r → ZMod 2) (p : Fin M → ℚ)
          (Dl : List (Fin r → ZMod 2)) (z : Fin r → ZMod 2) (a : Fin M → ℚ) (H : ℕ),
          2 ≤ Dl.toFinset.card → z ∈ Dl → (∀ k, a k ≤ 1) →
          IsMenuCertificate ell {y | y ∈ Dl} z (fun k => (a k : ℝ)) →
          (∀ k, 1 / 8 ≤ p k ∧ p k ≤ 3 / 8) → 1 ≤ H →
          (∀ (ρ : Tape) (l : List (Fin M × ZMod 2)), ∃ n : ℕ,
            (mrun prog (encVerifierInput ell p Dl z a H ++ encPLog l) ρ n).halted = true) ∧
          (procOfProgram (M := M) (fun b : Bool => [b]) false prog
              (encVerifierInput ell p Dl z a H)).IsMeasurable ∧
            VerifierSpec ell (fun k => (p k : ℝ)) Dl.toFinset z (∑ k, (a k : ℝ)) H C
              (procOfProgram (fun b : Bool => [b]) false prog
                (encVerifierInput ell p Dl z a H)) := by sorry

end InteractionElim.Main
