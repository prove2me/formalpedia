-- Prove2me | Theorems.Thm_KedlayaUmans_FrobeniusLift_frobenius_congruence
-- name    : KedlayaUmans.FrobeniusLift.frobenius_congruence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:49:27.237852+00:00
-- url     : https://prove2.me/theorems/480dabcf-a507-4f15-849e-a36114903739
-- title:
--   §6, p. 19 — η is fixed by σ, and (g(Z))^{h^i} ≡ σ^i(g)(η^i Z) (mod E(Z))
-- statement:
--   Let $p$ be a prime, $\mathbb F_q$ a finite field of characteristic $p$, $P \in \mathbb F_p[W]$ irreducible over $\mathbb F_p$ of degree $c$, $h = p^c$, $K = \mathbb F_p[W]/(P(W)) \subseteq R = \mathbb F_q[W]/(P(W))$, $\eta$ a primitive element of $K$ (multiplicative order $h-1$), and $E(Z) = Z^{h-1} - \eta \in R[Z]$. Let $\sigma^i : R \to R$ be $x \mapsto x^{h^i}$, and for $g \in R[Z]$ let $\sigma^i(g)$ be the polynomial obtained by applying $\sigma^i$ to the coefficients of $g$. Then
--
--   1. $\eta$ is fixed by $\sigma$: $\eta^h = \eta$ in $R$;
--   2. for every $g \in R[Z]$ and every $i \ge 0$,
--   $$(g(Z))^{h^i} \equiv \sigma^i(g)(\eta^i Z) \pmod{E(Z)}.$$
--
--   This is the display in the proof of Lemma 6.1: raising to the $h^i$-th power is $\sigma^i$ on the coefficients together with $Z \mapsto Z^{h^i}$, and modulo $E$ the latter becomes multiplication of the variable by $\eta^i$.
--
--   **Formalization Note** The congruence is stated as an equality of residue classes in $S = R[Z]/(E(Z))$, for every $g$ (the paper applies it to $g_\alpha$).
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), p. 19, proof of Lemma 6.1 (unnumbered display)

import Mathlib
import Definitions.Def_KedlayaUmans_FrobeniusLift_Setup
import Definitions.Def_KedlayaUmans_FrobeniusLift_LiftProject

open Polynomial

namespace KedlayaUmans.FrobeniusLift

/-- §6, p. 19, display in the proof of Lemma 6.1: `η` is fixed under `σ`, and for every `g ∈ R[Z]` and
every `i`, `(g(Z))^{h^i} ≡ σ^i(g)(η^i Z) (mod E(Z))`, where `σ^i(g)` applies `σ^i` to the coefficients. -/
theorem frobenius_congruence (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Fintype F] [CharP F p]
    (P : (ZMod p)[X]) [Fact (Irreducible P)]
    (η : K p P) (hη : IsPrimitiveRoot η (h p P - 1)) :
    sigma p F P 1 (ι p F P η) = ι p F P η ∧
      ∀ (g : (R p F P)[X]) (i : ℕ),
        AdjoinRoot.mk (E p F P η) (g ^ (h p P ^ i)) =
          AdjoinRoot.mk (E p F P η) ((g.map (sigma p F P i)).comp (C (ι p F P η ^ i) * X)) := by sorry

end KedlayaUmans.FrobeniusLift
