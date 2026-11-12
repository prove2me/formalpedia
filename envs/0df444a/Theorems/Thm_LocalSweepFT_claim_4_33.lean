-- Prove2me | Theorems.Thm_LocalSweepFT_claim_4_33
-- name    : LocalSweepFT.claim_4_33
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:44:09.929546+00:00
-- url     : https://prove2.me/theorems/72b22c51-b731-4e4b-8e60-51ee2b9f8821
-- title:
--   Claim 4.33 — the Hadamard-type gate $H_\phi$ is realized by $\phi\circ H^{\otimes F^n_{d'}}$
-- statement:
--   Let $1\le d'<d$, $n\ge1$, and $\hat H_\phi=\phi\circ H^{\otimes F^n_{d'}}$, from the side-$n$ $(d,d')$-Toric code to the $(d,d-d')$-Toric code.
--   1. The transpose map intertwines boundaries and coboundaries in every dimension: $\phi\,\partial^-=\partial^+\phi$ and $\phi\,\partial^+=\partial^-\phi$; so $\phi$ sends Z-stabilizers of one code to X-stabilizers of the other and vice versa.
--   2. $\phi(x_{S'})=z_{S/S'}$, and $\phi(z_{S'})+x_{S/S'}$ is an X-stabilizer of the dual code; so $H_\phi(X_{S'})=Z_{S/S'}$ and $H_\phi(Z_{S'})=X_{S/S'}$ as logical operators (Def. 4.32).
--   3. For every $d'$-chain $c$: $\hat H_\phi X^c\hat H_\phi^\dagger=Z^{\phi(c)}$ and $\hat H_\phi Z^c\hat H_\phi^\dagger=X^{\phi(c)}$.
--   4. $\hat H_\phi$ maps the code space of the $(d,d')$-Toric code onto that of the $(d,d-d')$-Toric code.
--
--   This is what lets the same sweep rule correct both the bit-flip and the phase-flip sector.
--
--   Differences from the source:
--   - reading: Def 4.32: H_ϕ(Z_{S′}) → X_{S/S′} → ϕ(z_{S′}) + x_{S/S′} ∈ im ∂⁻ of the dual code; reason: ϕ(z_{S′}) is the translate of x_{S/S′} by the vector Σ_{g∈S′} g, a homologous cycle; the logical equality is equality up to stabilizers, and exact equality fails for n ≥ 2
--   - encoding: "ϕ ∘ H^{⊗F^n_{d′}} realizes the logical isomorphism H_ϕ" → parts 1–4 (intertwining, logical operators, Pauli conjugation, code spaces); reason: the content of the proof on pp.33–34
--   - generalization: ϕ intertwines ∂⁻ and ∂⁺ on the stabilizer dimensions (pp.33–34) → in every dimension i, j with i + 1 + j = d; reason: the paper's computation is the same for every dimension; the stabilizer dimensions are a special case
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Claim 4.33 with Definition 4.32, pp.33–34

import Mathlib
import Definitions.Def_LocalSweepFT_Chain
import Definitions.Def_LocalSweepFT_xLog
import Definitions.Def_LocalSweepFT_liftOn
import Definitions.Def_LocalSweepFT_encMat
import Definitions.Def_LocalSweepFT_sweepCycleKraus

open Matrix

namespace LocalSweepFT

/-- Claim 4.33 with Definition 4.32, p.33 (Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…)). The Hadamard-type gate `H_ϕ`,
a code isomorphism from the side-`n` `(d, d′)`-Toric code to the `(d, d − d′)`-Toric code
(`1 ≤ d′ < d`), is realized by `Ĥ_ϕ = ϕ ∘ H^{⊗F^n_{d′}}`:
1. `ϕ` intertwines the boundary and coboundary maps in every dimension (`ϕ∂⁻ = ∂⁺ϕ` and
   `ϕ∂⁺ = ∂⁻ϕ`), so it sends the Z-stabilizers of one code to the X-stabilizers of the other and
   vice versa (pp.33–34);
2. `ϕ(x_{S′}) = z_{S/S′}`, and `ϕ(z_{S′})` equals `x_{S/S′}` up to an X-stabilizer of the dual code,
   so `H_ϕ(X_{S′}) = Z_{S/S′}` and `H_ϕ(Z_{S′}) = X_{S/S′}` as logical operators (Def 4.32);
3. `Ĥ_ϕ X^c Ĥ_ϕ† = Z^{ϕ(c)}` and `Ĥ_ϕ Z^c Ĥ_ϕ† = X^{ϕ(c)}` for every `d′`-chain `c`;
4. `Ĥ_ϕ` maps the code space of the `(d, d′)`-Toric code onto that of the `(d, d − d′)`-Toric code.

**Formalization Note.** `ϕ(z_{S′})` is the translate of `x_{S/S′}` by `S′`, a homologous cycle, so
part 2 states the logical equality of Def 4.32 for `Z_{S′}` modulo stabilizers. -/
theorem claim_4_33 (d d' n : ℕ) [NeZero n] (h1 : 1 ≤ d') (h2 : d' < d) :
    (∀ (i j : ℕ) (h : i + 1 + j = d) (h' : i + (j + 1) = d) (x : Chain (ZMod n) d (i + 1)),
      phiChain h' (bdry x) = cobdry (phiChain h x)) ∧
    (∀ (i j : ℕ) (h : i + (j + 1) = d) (h' : i + 1 + j = d) (x : Chain (ZMod n) d i),
      phiChain h' (cobdry x) = bdry (phiChain h x)) ∧
    (∀ S : DirSet d d', phiChain (Nat.add_sub_cancel' h2.le) (xLog (n := n) S) = zLog S.compl) ∧
    (∀ S : DirSet d d', phiChain (Nat.add_sub_cancel' h2.le) (zLog (n := n) S) + xLog S.compl ∈
      bdryRange (ZMod n) d (d - d')) ∧
    (∀ c : QCell d d' n → ZMod 2,
      dualU (n := n) (Nat.add_sub_cancel' h2.le) * xOn c *
        (dualU (n := n) (Nat.add_sub_cancel' h2.le)).conjTranspose =
        zOn ⇑(phiChain (Nat.add_sub_cancel' h2.le) (toChain c))) ∧
    (∀ c : QCell d d' n → ZMod 2,
      dualU (n := n) (Nat.add_sub_cancel' h2.le) * zOn c *
        (dualU (n := n) (Nat.add_sub_cancel' h2.le)).conjTranspose =
        xOn ⇑(phiChain (Nat.add_sub_cancel' h2.le) (toChain c))) ∧
    (codeSpace d d' n).map (Matrix.mulVecLin (dualU (n := n) (Nat.add_sub_cancel' h2.le))) =
      codeSpace d (d - d') n := by sorry

end LocalSweepFT
