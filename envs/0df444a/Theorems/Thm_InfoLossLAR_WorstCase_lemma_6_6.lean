-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_lemma_6_6
-- name    : InfoLossLAR.WorstCase.lemma_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:05:22.232911+00:00
-- url     : https://prove2.me/theorems/cc9c72bc-c4ab-4a92-b5a1-c1b6e4e86e22
-- title:
--   Lemma 6.6 — endpoint and carry bound $\Delta(\mathcal L(x'),U(\mathcal F_{T,0}))\le\Delta(\mathcal L(\bar w),U(H_0))+\Pr[k\notin\mathcal L(T)]$
-- statement:
--   Let $q$ be an odd prime, $d\ge q$ and $T$ the matrix of Definition 6.3. Let the source $x$ have an arbitrary law $\mu$ on $\mathbb F_q^d$, and let $(Q,\beta)\in\mathbb Z^{d\times d}\times\mathbb Z^d$ be drawn independently of $x$ from a (countable) law $\nu$ supported on pairs with $Q\bmod q\in\mathrm{GL}_d(\mathbb F_q)$. With the load $w=T(Q[x]_q+\beta)$ (Definition 6.1), its carry $k=\lfloor w/q\rfloor$, the output $x'=(Q[x]_q+\beta)\bmod q$ and the endpoint $\bar w=w\bmod q=Tx'\bmod q\in H_0$,
--   $$\Delta\big(\mathcal L(x'),U(\mathcal F_{T,0})\big)\le\Delta\big(\mathcal L(\bar w),U(H_0)\big)+\Pr[k\notin\mathcal L(T)],$$
--   laws and probability over both $(Q,\beta)$ and $x$. The exact pointwise criterion is
--   $$x'=c_T(\bar w)\iff k\in\mathcal L(T)\iff\mathbf 1^\top k\equiv0\pmod q .$$
--
--   Differences from the source:
--   - generalization: $x\leftarrow\chi_G$ → $x$ with an arbitrary law $\mu$ on $\mathbb F_q^d$; reason: the coupling argument never uses the Gaussian law; $\mu=\chi_G$ is the source's case
--   - generalization: the pointwise criterion (stated under the lemma's hypotheses) → for every $x$ and every integer pair $(Q,\beta)$, invertible mod $q$ or not; reason: the identity does not use invertibility; it contains the source's case
--   - encoding: "$\bar w:=w\bmod q=Tx'\bmod q\in H_0$" → two pointwise clauses ($w\bmod q=T[x']_q\bmod q$, and $w\bmod q\in H_0$); reason: the definition asserts both
--   - encoding: probabilities over $(Q,\beta)$ → sums $\sum'_{(Q,\beta)}\nu(Q,\beta)\sum_x\mu(x)[\cdot]$; reason: a countable law
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 28, Lemma 6.6

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_Rounding
import Definitions.Def_InfoLossLAR_WorstCase_FixedT
import Definitions.Def_InfoLossLAR_WorstCase_Laws

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

/-- Lemma 6.6 (Endpoint and carry bound for affine transport), p. 28, with an arbitrary source
law. `q` is an odd prime, `d ≥ q`, `T` is the matrix of Definition 6.3; the source `x ← μ` on
`𝔽_q^d` and the transport pair `(Q, β) ← ν` on `ℤ^{d×d} × ℤ^d` (a countable law supported on
pairs with `Q mod q ∈ GL_d(𝔽_q)`) are independent. With the load `w = T(Q[x]_q + β)`, carry
`k = ⌊w/q⌋`, output `x' = (Q[x]_q + β) mod q` and endpoint `w̄ = w mod q`:
`Δ(L(x'), U(F_{T,0})) ≤ Δ(L(w̄), U(H_0)) + Pr[k ∉ L(T)]`. Moreover, for every `x, Q, β`,
`w̄ = Tx' mod q ∈ H_0`, and `x' = c_T(w̄) ⟺ k ∈ L(T) ⟺ 1ᵀk ≡ 0 (mod q)`. -/
theorem lemma_6_6 (q d : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hdq : q ≤ d)
    (μ : (Fin d → ZMod q) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (ν : Matrix (Fin d) (Fin d) ℤ × (Fin d → ℤ) → ℝ) (hν0 : ∀ p, 0 ≤ ν p) (hν1 : HasSum ν 1)
    (hνinv : ∀ p, ν p ≠ 0 → IsUnit (matModq q p.1).det) :
    sdist
        (fun z => ∑' p, ν p * ∑ x, if modq q (p.1.mulVec (lift x) + p.2) = z then μ x else 0)
        (unifOn (Finset.univ.filter fun x : Fin d → ZMod q => fT63 q d x = 0)) ≤
      sdist
          (fun z => ∑' p, ν p *
            ∑ x, if modq q (incidenceLoad q d p.1 p.2 (lift x)) = z then μ x else 0)
          (unifOn (Finset.univ.filter fun w : Fin d → ZMod q => ∑ i, w i = 0)) +
        ∑' p, ν p * ∑ x, (open Classical in
          if carry q (incidenceLoad q d p.1 p.2 (lift x)) ∈ imageLattice (TDef63 q d)
          then 0 else μ x) ∧
    ∀ (Q : Matrix (Fin d) (Fin d) ℤ) (β : Fin d → ℤ) (x : Fin d → ZMod q),
      modq q (incidenceLoad q d Q β (lift x)) =
        modq q ((TDef63 q d).mulVec (lift (modq q (Q.mulVec (lift x) + β)))) ∧
      modq q (incidenceLoad q d Q β (lift x)) ∈ H0 q d ∧
      (modq q (Q.mulVec (lift x) + β) = cT q d (modq q (incidenceLoad q d Q β (lift x))) ↔
        carry q (incidenceLoad q d Q β (lift x)) ∈ imageLattice (TDef63 q d)) ∧
      (carry q (incidenceLoad q d Q β (lift x)) ∈ imageLattice (TDef63 q d) ↔
        (q : ℤ) ∣ ∑ j, carry q (incidenceLoad q d Q β (lift x)) j) := by sorry

end InfoLossLAR.WorstCase
