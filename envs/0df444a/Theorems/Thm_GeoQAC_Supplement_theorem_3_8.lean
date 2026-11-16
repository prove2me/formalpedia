-- Prove2me | Theorems.Thm_GeoQAC_Supplement_theorem_3_8
-- name    : GeoQAC.Supplement.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:22:25.536211+00:00
-- url     : https://prove2.me/theorems/0b762264-cb10-4366-a959-690911aabd56
-- title:
--   Theorem 3.8 — width lower bounds for cat-state and Dicke-state synthesis
-- statement:
--   There is an absolute constant $c>0$ with the following property. Let $C$ be a $[w,h]$-2D-QAC circuit of depth $d\ge1$ (with $w\ge1$ rows), started from $|0\cdots0\rangle$, with $n$ target qubits at arbitrary positions and the other qubits as ancillas.
--
--   1. If $C$ synthesizes $|\mathrm{cat}_n\rangle$ with target-marginal squared fidelity at least $1-\eta^2$ for some $0\le\eta\le 1/8$, then
--   $$
--   c\,n^{1/(3d+1)}\le w .
--   $$
--   2. If $0\le k\le n$ and $C$ synthesizes the Dicke state $|D_{n,k}\rangle$ exactly (target-marginal fidelity $1$), then
--   $$
--   c\,\big(1+\min\{k,n-k\}\big)^{1/(3d+1)}\le w .
--   $$
--
--   No number of ancillas helps: correlated states need a grid whose width grows polynomially in $n$ at every fixed depth.
--
--   Differences from the source:
--   - encoding: w = Ω(·) → one absolute c > 0, chosen before d, with the bound for every n; reason: §2.1 (p.9) makes implicit constants absolute; the proof's bound 59n/64 ≤ K^d w^{3d+1} holds for every n
--   - encoding: a width-w rectangle → 0 < w; reason: a grid with no rows has no qubits; this only excludes the empty layout
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Theorem 3.8, p.16

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_Supplement_targetFidelity
import Definitions.Def_GeoQAC_Supplement_catVec

namespace GeoQAC.Supplement

open GeoQAC

/-- **Theorem 3.8** (Dong, Ou, Yao, arXiv:2604.07178, version of 2026-11-03, p.16). "Let `C` be a
depth-`d ≥ 1`, width-`w` 2D-QAC circuit starting from `|0^{n+a}⟩` on `n` target qubits and `a`
ancillas.
• If `C` synthesizes `|cat_n⟩` with target-marginal squared fidelity at least `1 − η²`, where
  `0 ≤ η ≤ 1/8`, then `w = Ω(n^{1/(3d+1)})`.
• For `0 ≤ k ≤ n`, if `C` synthesizes `|D_{n,k}⟩` exactly, then
  `w = Ω((1 + min{k, n − k})^{1/(3d+1)})`."

**Formalization Note.**
* One absolute constant `c > 0`, chosen before `d` (§2.1, p.9: asymptotic notation hides absolute
  constants unless a dependence is stated).
* The circuit is a `[w, h]`-2D-QAC circuit on `Pos w h` started from `|0…0⟩`; the `n` targets sit at
  any injective placement `tgt`, every other qubit is an ancilla. Synthesis is target-marginal
  (Definition 2.6): `targetFidelity C tgt φ = ⟨φ|ρ_T|φ⟩`; exact synthesis is fidelity `1`.
* The rectangle has at least one row (`0 < w`); for `w = 0` there are no qubits at all.
* Real exponents `1/(3d+1)` (`Real.rpow`). -/
theorem theorem_3_8 : ∃ c : ℝ, 0 < c ∧
    ∀ (d w h n : ℕ) (C : QACCircuit (Pos w h) d) (tgt : Fin n ↪ Pos w h),
      1 ≤ d → 0 < w → C.Is2D →
      (∀ η : ℝ, 0 ≤ η → η ≤ 1 / 8 → 1 - η ^ 2 ≤ targetFidelity C tgt (catVec n) →
          c * (n : ℝ) ^ ((1 : ℝ) / (3 * (d : ℝ) + 1)) ≤ w) ∧
      (∀ k : ℕ, k ≤ n → targetFidelity C tgt (dickeVec n k) = 1 →
          c * ((1 + min k (n - k) : ℕ) : ℝ) ^ ((1 : ℝ) / (3 * (d : ℝ) + 1)) ≤ w) := by sorry

end GeoQAC.Supplement
