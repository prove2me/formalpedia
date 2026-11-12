-- Prove2me | Theorems.Thm_NarrowDNF_Approx_lemma_4_1
-- name    : NarrowDNF.Approx.lemma_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:33.16598+00:00
-- url     : https://prove2.me/theorems/8317f199-f462-47ed-bbf1-dbeebe6c3f7d
-- title:
--   Lemma 4.1 — The active 1-coordinates form a positive certificate
-- statement:
--   Let $J$ have increasing activations and let $u$ be increasing and $\mathcal F_J$-measurable. Put $T(x)=\{i\in A_J(x):x_i=1\}$. For every accepted input $x$, the set $T(x)$ is a positive certificate:
--   $$u(x)=1\ \Longrightarrow\ \forall y,\ (\forall i\in T(x),\ y_i=1)\Longrightarrow u(y)=1.$$
--   For every nonnegative integer $w$, let $g_w$ be precisely the truncated DNF of Eq. (7), as defined in the certificate interface. It is increasing, has width at most $w$, satisfies $g_w\le u$, and obeys the entire chain
--   $$\mathbb P_p[u\ne g_w]\le\mathbb P_p[|T(X)|>w]\le\frac{\mathbb E_p|A_J(X)|}{w+1}.$$
--   Probability uses the standing $0<p<1$ convention. Width zero and both constant functions are permitted. The certificate assertion is pointwise, not merely almost sure. This connects adaptive information to a concrete family of short positive terms.
--
--   Differences from the source:
--   - encoding: coordinates [n] and bits {0,1} → Fin n and Bool with pointwise false < true; reason: coordinate relabeling preserves all source instances
--   - encoding: product probabilities and expectations → published Bernoulli event sums and exact real finite weighted sums; reason: the finite product law is identical and every cost is integrable
--   - encoding: local activations and F_J-measurability → functions on S → Bool and constancy on equal dependent-pair atoms; reason: locality and precisely the recorded adaptive information are preserved
--   - encoding: nonnegative integer cutoffs → natural numbers; reason: the domains coincide, including zero
--   - encoding: the disjunction indexed by all accepted x with |T(x)|≤w → the defined finite image of their active-one sets, with duplicate terms removed; reason: duplicate disjuncts change neither evaluation nor maximum width; no arbitrary approximator replaces Eq. (7)
--   - encoding: P_p and E_p under the standing p∈(0,1) convention → explicit hypotheses 0<p and p<1; reason: Section 1 fixes this probability domain; the certificate and width clauses do not otherwise depend on the bias
-- source:
--   Chenghua Liu, Boning Meng, STOC 2027 submission #1509 (October 2026), Lemma 4.1, Eqs. (7)–(8), p. 8 (PDF p. 9)

import Definitions.Def_NarrowDNF_Approx_Certificates

namespace NarrowDNF.Approx

theorem lemma_4_1 {n : ℕ} (p : ℝ) (J : ActivationFamily n) (u : Cube n → Bool)
    (hp : 0 < p) (hp_one : p < 1) (hJ : IncreasingActivations J)
    (hu : Monotone u) (humeas : AdaptiveMeasurable J u) :
    (∀ x, u x = true → PositiveCertificate u (activeOnes J x)) ∧
    (∀ w : ℕ, width (truncatedDNF J u w) ≤ w ∧ Monotone (evalDNF (truncatedDNF J u w)) ∧
      (∀ y, evalDNF (truncatedDNF J u w) y ≤ u y) ∧
      error p u (evalDNF (truncatedDNF J u w)) ≤
        prob p (fun x => w < (activeOnes J x).card) ∧
      prob p (fun x => w < (activeOnes J x).card) ≤ activeCost p J / ((w : ℝ) + 1)) := by sorry

end NarrowDNF.Approx
