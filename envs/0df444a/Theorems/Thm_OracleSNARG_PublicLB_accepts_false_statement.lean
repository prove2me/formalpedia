-- Prove2me | Theorems.Thm_OracleSNARG_PublicLB_accepts_false_statement
-- name    : OracleSNARG.PublicLB.accepts_false_statement
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:48:27.709108+00:00
-- url     : https://prove2.me/theorems/c30944f7-fcf1-47f5-9b0e-1d09ab206d99
-- title:
--   §6, Analysis — on $E_{\mathrm{crs},r}$ the verifier accepts a false statement, and $|B_{\mathrm{crs},r}|\le\ell$
-- statement:
--   Fix $\lambda$ and a scheme $S=(\mathrm{Gen},P,V)$ whose verifier makes at most $\ell=\ell(\lambda)$ oracle queries on every input, against every oracle, with $8\ell\le N=N(\lambda)$. Let $\mathrm{crs}$ satisfy $|\mathrm{crs}|<n=n(\lambda)$ and let $r$ be prover coins with
--   $$V^{O_1}(\mathrm{crs},x_{\mathrm{crs}},\pi_{\mathrm{crs},r})=1 .$$
--   Then $|B_{\mathrm{crs},r}|\le\ell$. Moreover, for every $h:\{0,1\}^n\to\{0,1\}^k$ for which the event $E_{\mathrm{crs},r}$ holds ($h(x_{\mathrm{crs}})=0^k$ and $h(u)\ne0^k$ for all $u\in B_{\mathrm{crs},r}$),
--   $$C^{O_{h,r}}(x_{\mathrm{crs}})=0\qquad\text{and}\qquad V^{O_{h,r}}(\mathrm{crs},x_{\mathrm{crs}},\pi_{\mathrm{crs},r})=1 ,$$
--   so the verifier accepts the false statement $x_{\mathrm{crs}}\notin L^{O_{h,r}}$ with the proof that the cheating prover outputs.
--
--   Differences from the source:
--
--   - generalization: h a sample of the pairwise-independent family → any function h : {0,1}^n → {0,1}^k on which E_{crs,r} holds; reason: the claim is pointwise in h, so it specializes to the paper's
--   - generalization: a SNARG (Gen, P, V) with polynomial-time algorithms (Definition 9), k = log2(2ℓ), and crs sampled from Gen → any scheme (no efficiency or completeness assumed), any output length k of h, and any crs with |crs| < n(λ); reason: the step uses only the query bound ℓ ≤ N/8 of V and n > |crs| (footnote 7), so it specializes to the paper's
--   - reading: "the verifier accepts a false statement" → C^{O_{h,r}}(x_crs) = 0 and V^{O_{h,r}}(crs, x_crs, π_{crs,r}) = 1; reason: the statement is x_crs and the proof is π_{crs,r}, as output by the cheating prover P*_r; its robustness is the separate Robustness milestone
--   - encoding: |B_{crs,r}| → the extended-natural cardinality Set.encard of the set B_{crs,r}; reason: an infinite set would have encard ⊤, so the bound is not vacuous
-- source:
--   Goldwasser, Kalai, Incrementally Verifiable Oracle Aided Computation, STOC 2027 submission (manuscript sha256 cc66f0af…), p. 26, §6, Analysis ('It is easy to see that on this event, the verifier accepts a false statement')

import Mathlib
import Definitions.Def_OracleSNARG_PublicLB_Majority
import Definitions.Def_OracleSNARG_PublicLB_Scheme
import Definitions.Def_OracleSNARG_PublicLB_ProofObjects

set_option autoImplicit false

namespace OracleSNARG.PublicLB

/-- **§6, Analysis**, p. 26 of Goldwasser, Kalai (manuscript sha256 cc66f0af…): "Fix crs, r for
which V^{O1}(crs, x_crs, π_{crs,r}) = 1. … We have |B_{crs,r}| ≤ ℓ. Consider the event E_{crs,r} …
It is easy to see that on this event, the verifier accepts a false statement." At a fixed `λ`, for a
verifier making at most `ℓ(λ) ≤ N(λ)/8` queries on every input and `|crs| < n(λ)`: always
`|B_{crs,r}| ≤ ℓ`, and on `E_{crs,r}` we get `C^{O_{h,r}}(x_crs) = 0` and
`V^{O_{h,r}}(crs, x_crs, π_{crs,r}) = 1`. -/
theorem accepts_false_statement (n N ℓ : ℕ → ℕ) (S : Scheme) (lam : ℕ)
    (hV : ∀ crs x π, (S.verifier lam crs x π).depth ≤ ℓ lam)
    (hℓN : 8 * ℓ lam ≤ N lam) (crs : List Bool) (hcrs : crs.length < n lam)
    (r : Fin (S.prover lam).coins → Bool)
    (hacc : (verifierRun S n lam crs r).eval O1 = true)
    {k : ℕ} (h : Hash (n lam) k) (hE : EventE S n N lam crs r h) :
    (Bset S n N lam crs r).encard ≤ (ℓ lam : ℕ∞) ∧
      C (Ohr S n N lam h r) (N lam) (xcrs (n lam) crs) = false ∧
      (verifierRun S n lam crs r).eval (Ohr S n N lam h r) = true := by sorry

end OracleSNARG.PublicLB
