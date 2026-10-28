-- Prove2me | Theorems.Thm_NechitaRDM_MP_lemma_1
-- name    : NechitaRDM.MP.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:45.813842+00:00
-- url     : https://prove2.me/theorems/4c05d5be-3087-43fb-99b9-c845ac880e82
-- title:
--   Lemma 1, p. 6 — for an n × k matrix X with i.i.d. N_ℂ(0,1) entries, ρ = XX*/Tr(XX*) has distribution μ_{n,k}
-- statement:
--   Let $n, k \ge 1$ and let $X$ be a random $n\times k$ complex matrix whose entries are independent and identically distributed with law $\mathcal N_{\mathbb C}(0,1)$. Then the random matrix
--   $$\rho = \frac{X X^*}{\operatorname{Tr}(X X^*)}$$
--   has distribution $\mu_{n,k}$, the induced measure of Definition 3.
--
--   This is the bridge between random density matrices and the Wishart ensemble $W = XX^*$: every result on Wishart matrices transfers to $\mu_{n,k}$ through $\rho = W/\operatorname{Tr} W$.
--
--   **Formalization Note** $n \ge 1$ and $k \ge 1$ are implicit in "a $n \times k$ complex matrix" and in the definition of $\mu_{n,k}$ (there are no pure states in dimension $0$); they are stated. The event $X = 0$ (where Lean sets $\rho = 0$) is $P$-null.
-- source:
--   Nechita, Asymptotics of random density matrices, arXiv:quant-ph/0702154v3, p. 6, Lemma 1 (eq. (15))

import Mathlib
import Definitions.Def_NechitaRDM_MP_Basic

namespace NechitaRDM.MP

open MeasureTheory

/-- **Lemma 1** (p. 6). If `X` is an `n × k` complex matrix with i.i.d. `N_ℂ(0,1)` entries,
then `ρ = XX* / Tr(XX*)` has distribution `μ_{n,k}`. -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (X : Ω → Matrix (Fin n) (Fin k) ℂ)
    (hX : IsComplexGaussianMatrix P X) :
    HasInducedLaw P (fun ω => (wishart (X ω)).trace⁻¹ • wishart (X ω)) k := by sorry

end NechitaRDM.MP
