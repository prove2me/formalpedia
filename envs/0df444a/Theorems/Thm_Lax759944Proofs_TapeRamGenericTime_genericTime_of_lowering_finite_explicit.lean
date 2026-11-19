-- Prove2me | Theorems.Thm_Lax759944Proofs_TapeRamGenericTime_genericTime_of_lowering_finite_explicit
-- name    : Lax759944Proofs.TapeRamGenericTime.genericTime_of_lowering_finite_explicit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:30:58.718044+00:00
-- url     : https://prove2.me/theorems/c5a061ef-9537-44f4-af74-475e7563d805
-- title:
--   Finite tape simulation with the explicit interpreter clock
-- statement:
--   Suppose a lowering sends every finite word-RAM program to the legacy RAM and simulates $t$ steps at width $v$ within $18t+6(|x|+1)+26$ steps at width $v+1$, whenever the encoded input and its length satisfy the stated width guards. Suppose also that the binary encoding length $b(x)$ is at least $|x|$. For every program $p$ and natural-coefficient width polynomial $W$, there is a single tape machine with finite alphabets and a width-overhead polynomial $W'\ge W$. Every run of $p$ on $|x|::x$ producing $y$ at width $W'(b(x))$ is simulated on the binary word encodings, provided $|x|::x$ and $y$ fit width $W(b(x))$.
--
--   Its actual tape execution is bounded by
--   $$P_{\operatorname{compile}(\operatorname{lower}(p)),\,W+X+7,\,X}\bigl(100(b(x)+t+1)\bigr),$$
--   where $P$ is the explicit interpreter time polynomial from the published operational definitions. Input and output alphabets are transported by the machine's encoding equivalences. This supplies a finite deterministic realization with a concrete clock, rather than an assigned abstract running time.
-- source:
--   https://github.com/szymtor/RAM-TM/blob/134e398cef46599371df99f10c9007bc34ba3868/proofs/Lax759944Proofs/TapeRamGenericTime.lean, theorem genericTime_of_lowering; mission-local explicit finite-alphabet refinement in Solutions/VerifiedRamToTMExplicitSource.lean, theorem genericTime_of_lowering_finite_explicit, using the explicit RamToTM interpreter clock.

import Definitions.Def_EdgeSublinearMWIS_Main_NativeOperationalInterfaces

theorem Lax759944Proofs.TapeRamGenericTime.genericTime_of_lowering_finite_explicit : ∀ (lower : Lax808846.Ram.Program → Lax759944Proofs.Legacy.Ram.Program),
  (∀ (p : Lax808846.Ram.Program) (v : ℕ) (x output : List ℕ) (t : ℕ),
      (∀ a ∈ x.length :: x, a < 2 ^ v) →
        x.length + 33 < 2 ^ v →
          Lax808846.Ram.RunsTo v p (x.length :: x) output t →
            ∃ u ≤ 18 * t + 6 * (x.length + 1) + 26,
              Lax759944Proofs.Legacy.Ram.RunsTo (v + 1) (lower p) (x.length :: x) output u) →
    (∀ (x : List ℕ), x.length ≤ Lax759944.BinaryWordEncoding.bitSize x) →
      ∀ (p : Lax808846.Ram.Program) (wordBound : Polynomial ℕ),
        ∃ (H : Turing.TM2ComputableAux Lax759944.BinaryWordEncoding.Symbol Lax759944.BinaryWordEncoding.Symbol)
          (widthOverhead : Polynomial ℕ),
          (∀ (k : H.tm.K), Finite (H.tm.Γ k)) ∧
            (∀ (n : ℕ), Polynomial.eval n wordBound ≤ Polynomial.eval n widthOverhead) ∧
              ∀ (x output : List ℕ) (t : ℕ),
                Lax759944.RamPolytime.FitsInWords (Polynomial.eval (Lax759944.BinaryWordEncoding.bitSize x) wordBound)
                    (x.length :: x ++ output) →
                  Lax808846.Ram.RunsTo (Polynomial.eval (Lax759944.BinaryWordEncoding.bitSize x) widthOverhead) p
                      (x.length :: x) output t →
                    Nonempty
                      (Turing.TM2OutputsInTime H.tm
                        (List.map H.inputAlphabet.invFun (Lax759944.BinaryWordEncoding.encode x))
                        (Option.some (List.map H.outputAlphabet.invFun (Lax759944.BinaryWordEncoding.encode output)))
                        (Polynomial.eval (Lax759944.BinaryWordEncoding.bitSize x + t)
                          ((Lax759944Proofs.RamToTM.ramToTMTimePolynomial
                                (Lax759944Proofs.CellToMicrocode.compile (lower p))
                                (wordBound + Polynomial.X + Polynomial.C 7) Polynomial.X).comp
                            (Polynomial.C 100 * (Polynomial.X + 1))))) := by sorry
