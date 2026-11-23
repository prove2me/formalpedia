-- Prove2me | Theorems.Thm_LindbladTolerant_Testing_dephasing_family_facts
-- name    : LindbladTolerant.Testing.dephasing_family_facts
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:00:47.549189+00:00
-- url     : https://prove2.me/theorems/cb7a7bca-a51a-4cb7-b421-b7ba393f5563
-- title:
--   Theorem 5.2 — locality and norms of the dephasing hard family
-- statement:
--   Let $n,k\ge1$ and $\Gamma\ge0$. Consider the $n$-qubit dephasing generator
--   $$
--   \mathcal L_\Gamma(X)=\Gamma(Z_1XZ_1-X),
--   $$
--   where $Z_1$ acts as Pauli $Z$ on the first qubit and as the identity elsewhere.
--
--   The generator admits a traceless representation by the single jump $\sqrt\Gamma Z_1$, with zero Hamiltonian, so it has locality at most $k$. Its canonical dissipator is $\mathcal L_\Gamma$ itself, and the exact strength and diamond norm are
--   $$
--   \|\mathcal D_\Gamma\|_F=\sqrt2\,\Gamma,
--   \qquad
--   \|\mathcal L_\Gamma\|_\diamond=2\Gamma.
--   $$
--   These are Eqs.(112)–(114). In particular, the normalized superoperator Frobenius norm and the diamond norm are computed as defined in the mission, not assumed.
--
--   The zero rate $\Gamma=0$ is included. The statement supplies the exact YES/NO hard instances used at rates $\varepsilon_1/\sqrt2$ and $\varepsilon_2/\sqrt2$ in the proof of Theorem 5.2.
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238, Theorem 5.2 proof, Eqs.(111)–(115), pp.28–29. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf

import Definitions.Def_LindbladTolerant_Testing_lower_bound_model

set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
open scoped BigOperators Matrix ENNReal

namespace LindbladTolerant.Testing

theorem dephasing_family_facts (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (gamma : ℝ) (hgamma : 0 ≤ gamma) :
    LocalGenerator k (dephasing n gamma) ∧
    diamond (dephasing n gamma) = 2 * gamma ∧
    canonicalD (dephasing n gamma) = dephasing n gamma ∧
    frobenius (dephasing n gamma) = Real.sqrt 2 * gamma := by sorry
