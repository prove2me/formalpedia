-- Prove2me | Theorems.Thm_IntQuotHNP_per_input_cost
-- name    : IntQuotHNP.per_input_cost
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:53:46.636072+00:00
-- url     : https://prove2.me/theorems/1051a820-5e29-42ff-b9ca-30e4e4e88c8a
-- title:
--   Proof of Theorem 4.2 — per-input cost $\mathrm{poly}_N(\log p)[1+\min\{X,(KZ_{\mathrm{target}})^N\}]\le\mathrm{poly}_N(\log p)Z_{\mathrm{target}}^N$ (Theorem 3.4 and (2) for MIHNP)
-- statement:
--   There are one Turing machine $M$ and a step count $\tau(I)$ for each input such that $M$ outputs exactly the solution set of every promised input $I$ within $\tau(I)$ steps, and for each $N\ge3$ there are constants $C,K'$ such that every promised input with $N$ samples satisfies
--   $$
--   \tau(I)\le C(\log p)^{K'}\bigl[1+\min\{X,(KZ_{\mathrm{target}})^N\}\bigr]\quad\text{and}\quad\tau(I)\le C(\log p)^{K'}Z_{\mathrm{target}}^N .
--   $$
--   Here $Z_{\mathrm{target}}$ is that of the lattice (6) and $v_{\mathrm{tar}}$, and $K=1+12\sqrt d\,4^m$ with $m=d=N(N+1)/2$.
--
--   This is the deterministic per-input cost of the search, and the only way the running time depends on the input.
--
--   Differences from the source:
--   - reading: Algorithm 1 and its bit time → one Turing machine, chosen before N and the input, with a step count (OutputsWithin); reason: the paper names no machine; steps of a fixed multi-stack machine and bit operations are polynomially related, and the bounds are closed under polynomials
--   - encoding: Theorem 3.4 for a generic polynomial family and a reconstructor → its instance displayed in the proof of Theorem 4.2, with K taken from (2) at m = d = N(N + 1)/2; reason: the display is the source's statement for MIHNP; the generic theorem is not an item of this mission
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), proof of Theorem 4.2, p.24 (PDF p.25); Theorem 3.4 and eq. (2), p.20 (PDF p.21)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_IntQuotHNP_MIHNPInput
import Definitions.Def_IntQuotHNP_Encoding
import Definitions.Def_IntQuotHNP_DualLattice
import Definitions.Def_IntQuotHNP_MIHNPLattice

open HMBinPacking (OutputsWithin)

namespace IntQuotHNP

/-- **Proof of Theorem 4.2: the per-input cost `poly_N(log p)[1 + min{X, (KZ_target)^N}] ≤
poly_N(log p) Z_target^N`** (Theorem 3.4 with (2), instantiated for MIHNP).
Kang, Lee, *Provable Recovery from Integer Quotients*, STOC 2027 submission (manuscript sha256
605f9dd3…), proof of Theorem 4.2, p.24 (PDF p.25): "Thus the algorithm returns exactly the secrets
satisfying (4) with x ∈ B. … Since m, d depend only on N, the per-input cost is at most
poly_N(log p)[1 + min{X, (KZ_target)^N}] ≤ poly_N(log p)Z^N_target, where K is the constant in (2)."
Theorem 3.4, p.20 (PDF p.21); eq. (2), p.20: "K = 1 + 12√d 4^m".

There are one Turing machine `M` and a step count `τ(I)` for each input such that `M` outputs exactly
the solution set of every promised input `I` within `τ(I)` steps, and for each `N ≥ 3` there are
constants `C, K'` with, for every promised input with `N` samples,
`τ(I) ≤ C(log p)^{K'}[1 + min{X, (K Z_target)^N}]` and `τ(I) ≤ C(log p)^{K'} Z_target^N`, where
`Z_target` is that of the lattice (6) and `v_tar`, and `K = 1 + 12√d·4^m`, `m = d = N(N + 1)/2`.

**Formalization Note.** "Algorithm 1" is read as one Turing machine (`OutputsWithin`, step count),
chosen before `N` and the input; bit time and machine steps are polynomially related, and the
bounds are closed under polynomials. -/
theorem per_input_cost :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (τ : MIHNPInput → ℕ),
      (∀ I : MIHNPInput, IsPromised I →
        OutputsWithin M (encodeInput I) (encodeSecrets (solutionSet I)) (τ I)) ∧
      ∀ N : ℕ, 3 ≤ N → ∃ (C : ℝ) (K' : ℕ), ∀ I : MIHNPInput, IsPromised I → I.N = N →
        (τ I : ℝ) ≤ C * Real.log I.p ^ K' *
            (1 + min (I.X : ℝ) ((Kc N * zTarget (latticeBasis I) (vtar I) I.p) ^ N)) ∧
          (τ I : ℝ) ≤ C * Real.log I.p ^ K' * zTarget (latticeBasis I) (vtar I) I.p ^ N := by sorry

end IntQuotHNP
