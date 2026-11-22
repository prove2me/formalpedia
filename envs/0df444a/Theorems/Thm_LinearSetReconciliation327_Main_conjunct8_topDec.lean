-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_conjunct8_topDec
-- name    : LinearSetReconciliation327.Main.conjunct8_topDec
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-21T10:25:44.17917+00:00
-- url     : https://prove2.me/theorems/a80b058a-e008-48eb-bf06-611f3f6bd4f6
-- title:
--   Theorem 6.5, conjunct 8: the composite decoder recovers every d-sparse set with probability 1 - epsilon
-- statement:
--   **Conjunct 8 of Theorem 6.5 at the composite decoder.**  Let $S_{\mathrm{init}},S_{\mathrm{row}},S_{\mathrm{dec}},S_{\mathrm{assem}},S_{\mathrm{res}},S_{\mathrm{cr}}$ be the six compiled statements of the §9.2 decoder, and let
--
--   $$
--   \mathrm{progDecOfTop}(S_{\mathrm{init}},\dots,S_{\mathrm{cr}})
--   $$
--
--   be their composite, terminating in a `halt`.  Fix a table specification `spec`, a seed-indexed deterministic table `det`, a seed-indexed linear sketch $H_r\colon \mathbb{F}_2^n\to\mathbb{F}_2^M$, constants $C_d>0$ and $\varepsilon\ge 0$, and the decoding budget
--
--   $$
--   T_{\mathrm{dec}} \;=\; C_d\, d\, \exp\!\bigl(C_d\,(\lg\lg n)^2\bigr).
--   $$
--
--   Assume:
--
--   1. **the decoder halts** — for every seed $r$ and every stored payload $y\in\mathbb{F}_2^M$ there is a halting run of $\mathrm{progDecOfTop}$ under the environment $\mathrm{spec.env}(W,\mathrm{det},r)$, started from $\mathrm{decoderStart}(W,y,[])$, of length at most $T_{\mathrm{dec}}$ (this is conjunct 7);
--   2. **worst-case correctness per seed** — for every seed $r$, every $x\in\mathbb{F}_2^n$ and every *halting* run of $\mathrm{progDecOfTop}$ from $\mathrm{decoderStart}((\mathrm{spec.env}(W,\mathrm{det},r)).W, H_r x, [])$ of length at most $T_{\mathrm{dec}}$, the final state's output list is exactly $\operatorname{supp} x$.
--
--   Then for every $d$-sparse $x\in\mathbb{F}_2^n$,
--
--   $$
--   1-\varepsilon \;\le\; \Pr_{r}\Bigl[\;\exists s',\ \mathrm{HaltsWithin}\ \mathrm{progDecOfTop}\ (\mathrm{spec.env}(W,\mathrm{det},r))\ T_{\mathrm{dec}}\ \bigl(\mathrm{decoderStart}(W,H_r x,[])\bigr)\ s' \ \wedge\ \mathrm{OutputsSupport}\ s'\ x\;\Bigr].
--   $$
--
--   In words: the composite decoder recovers every $d$-sparse set from its sketch, except with probability at most $\varepsilon$ over the seed — which is exactly the last conjunct of `theorem_6_5`, with `progDec` instantiated at the composite and `Tdec` at the paper's budget.
--
--   **Why it is a theorem and not a restatement.**  The proof is *not* a composition of probabilities: because the correctness hypothesis is worst case and holds at every seed, the recovery event holds at *every* seed, so its probability is $1$, and $1-\varepsilon\le 1$ for $\varepsilon\ge0$.  The $\varepsilon$ of Theorem 6.5 can therefore only enter through the six stages' own failure probabilities, never through the composition.  The six stage contracts and their composition into hypothesis 2 are a separate node; hypothesis 1 is `haltsWithin_topDec_final`.
--
--   **Formalization Note** The submission is the 484-line block `Solutions/_65_correct_block.lean.txt` plus a root-level `theorem solution`; it imports only `Mathlib` and `Definitions.Def_LinearSetReconciliation327_Main_Top65Correct`, contains no `sorry`/`admit`, and `#print axioms solution` reports `[propext, Classical.choice, Quot.sound]`.  The hypothesis `hCorr` is written out rather than as the block's `C8.TopDecCorrectsSeed`, because the platform preamble may contain only `import Definitions.Def_*` lines and that predicate lives in the solution block; the two types are definitionally equal, and the proof file bridges them with a `have`.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5, PDF p.31 (printed p.30), last conjunct (`6toplevel.tex` lines 259-271, identical to Theorem 1.1); decoder of §9.2.  Proved in `Solutions/_65_correct_block.lean.txt`.

import Definitions.Def_LinearSetReconciliation327_Main_Top65Correct

namespace LinearSetReconciliation327.Main

theorem conjunct8_topDec {Sinit Srow Sdec Sassem Sres Scr : Stmt} {W M n d : ℕ} {spec : TableSpec}
    (det : ℕ → ℕ) (H : spec.Seed → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2))
    {Cd eps : ℝ} (heps : 0 ≤ eps)
    (hHalt : ∀ (r : spec.Seed) (y : Fin M → ZMod 2), ∃ s' : RAMState,
      HaltsWithin (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (spec.env W det r)
        (Cd * (d : ℝ) * Real.exp (Cd * lg (lg (n : ℝ)) ^ 2)) (decoderStart W y []) s')
    (hCorr : ∀ (r : spec.Seed) (x : Fin n → ZMod 2) (s' : RAMState),
      (∃ k : ℕ, (k : ℝ) ≤ Cd * (d : ℝ) * Real.exp (Cd * lg (lg (n : ℝ)) ^ 2) ∧
        (step (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (spec.env W det r))^[k]
          (decoderStart (spec.env W det r).W (H r x) []) = s' ∧
        Halted (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) s') →
      OutputsSupport s' x) :
    ∀ x : Fin n → ZMod 2, (Finset.univ.filter fun i => x i = 1).card ≤ d →
      1 - eps ≤ prU (fun r : spec.Seed => ∃ s' : RAMState,
        HaltsWithin (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (spec.env W det r)
          (Cd * (d : ℝ) * Real.exp (Cd * lg (lg (n : ℝ)) ^ 2))
          (decoderStart W (H r x) []) s' ∧
        OutputsSupport s' x) := by sorry

end LinearSetReconciliation327.Main
