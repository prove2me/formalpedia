-- Prove2me | Theorems.Thm_HypercliqueCircuits_Circuits_lemma_4
-- name    : HypercliqueCircuits.Circuits.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T00:35:58.659833+00:00
-- url     : https://prove2.me/theorems/6d58ae47-af65-4883-bbf3-eb115697ef26
-- title:
--   Lemma 4 — orthogonality and transpose eigenvalues
-- statement:
--   For labelled basis tensors $E_\sigma$ and $E_{\sigma'}$, let $u(\sigma)$ count off-diagonal factors. Every position $p$ satisfies all three identities:
--
--   $$\langle E_\sigma,E_{\sigma'}\rangle=\begin{cases}2^{u(\sigma)}&\sigma=\sigma',\\0&\sigma\ne\sigma',\end{cases}$$
--   $$\tau_pE_\sigma=\begin{cases}-E_\sigma&\sigma_p\text{ is skew},\\E_\sigma&\sigma_p\text{ is diagonal or symmetric},\end{cases}$$
--   $$(I-\tau_p)E_\sigma=\begin{cases}2E_\sigma&\sigma_p\text{ is skew},\\0&\sigma_p\text{ is diagonal or symmetric}.\end{cases}$$
--
--   The pairing is bilinear and the entries are integers, so no characteristic-two label collapse or conjugation convention changes these identities. They identify the basis used to analyze the computed low operator.
--
--   Differences from the source:
--   - encoding: one-based coordinate tuples and deletion of position j → Fin coordinates and functions on the ordered subtype of positions other than j; reason: the increasing-coordinate bijection preserves all variables and every monomial
--   - encoding: signed basis matrices and bilinear pairing over the characteristic-zero coefficient setting → the same matrices and equalities over the integers; reason: integer identities embed faithfully in the source dyadic ring
--   - generalization: q=2^B and the section-3 parameter assumptions → all natural q and d, without circuit or epsilon assumptions; reason: the three finite identities depend only on the defined basis and specialize to every source parameter choice
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, Lemma 4, p.18 (PDF 19).

import Definitions.Def_HypercliqueCircuits_Circuits_Transpose
import Definitions.Def_HypercliqueCircuits_Circuits_Machine

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits

/-- Lemma 4, printed p.18 / PDF 19. All three clauses, with labelled basis vectors. -/
theorem lemma_4 (q d : ℕ) :
    (∀ σ σ' : Label q d, frobenius (basisMatrix σ) (basisMatrix σ') =
      if σ = σ' then (2 : ℤ) ^ uCount σ else 0) ∧
    (∀ (σ : Label q d) (p : Fin d), applyOperator (tau {p}) (basisMatrix σ) =
      if skew (σ p) then -basisMatrix σ else basisMatrix σ) ∧
    (∀ (σ : Label q d) (p : Fin d),
      basisMatrix σ - applyOperator (tau {p}) (basisMatrix σ) =
      if skew (σ p) then (2 : ℤ) • basisMatrix σ else 0) := by sorry

end HypercliqueCircuits.Circuits
