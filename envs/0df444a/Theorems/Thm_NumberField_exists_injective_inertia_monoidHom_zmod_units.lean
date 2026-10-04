-- Prove2me | Theorems.Thm_NumberField_exists_injective_inertia_monoidHom_zmod_units
-- name    : NumberField.exists_injective_inertia_monoidHom_zmod_units
-- status  : Open
-- author  : @ebayuser
-- created : 2026-10-04T10:10:25.256718+00:00
-- url     : https://prove2.me/theorems/4ced357f-1584-41af-ad93-1b86464964e7
-- title:
--   Tame inertia of an abelian number field at $q$ embeds in $(\mathbb{Z}/q)^\times$
-- statement:
--   Let $K$ be a finite abelian extension of $\mathbb{Q}$ with group $G = \mathrm{Gal}(K/\mathbb{Q})$, let $q$ be a prime number, and let $Q$ be a prime ideal of the ring of integers $\mathcal{O}_K$ over $q$. Let
--
--   $$I = I(Q \mid q) = \{\sigma \in G : \sigma(x) \equiv x \pmod{Q} \text{ for all } x \in \mathcal{O}_K\}$$
--
--   be the inertia group. Assume that $q$ does not divide $|I|$ (the ramification at $Q$ is tame). The statement asserts that there is an injective group homomorphism
--
--   $$I \hookrightarrow (\mathbb{Z}/q\mathbb{Z})^\times .$$
--
--   Thus $I$ is cyclic and $|I|$ divides $q - 1$.
--
--   **Proof idea.** Let $\pi$ be a uniformizer at $Q$ and let $k = \mathcal{O}_K/Q$. The tame character $\theta(\sigma) = \sigma(\pi)/\pi \bmod Q$ is a homomorphism $I \to k^\times$ that does not depend on $\pi$. Its kernel is the wild inertia group, a $q$-group, which is trivial because $q \nmid |I|$. For $\tau$ in the decomposition group, $\theta(\tau\sigma\tau^{-1}) = \bar\tau(\theta(\sigma))$. The group $G$ is abelian, so $\theta(\sigma)$ is fixed by the image of the decomposition group, which is all of $\mathrm{Gal}(k/\mathbb{F}_q)$. Hence $\theta(\sigma) \in \mathbb{F}_q^\times$.
--
--   **Use.** This is the main missing piece of the tame step `NumberField.exists_isUnramifiedIn_le_sup_of_prime_ne` of the Kronecker-Weber theorem: it gives $|I| \mid q - 1$ for an abelian field of degree prime to $q$.
--
--   **Formalization Note.** `Q.inertia (K ≃ₐ[ℚ] K)` is Mathlib's `Ideal.inertia` for the action of the Galois group on `𝓞 K`. The hypothesis `hq` is not necessary for the truth of the statement (a prime ideal over `span {q}` exists only when `q` is prime or zero). Mathlib at this revision has `Ideal.card_inertia_eq_ramificationIdxIn`, the surjection from the decomposition group to the residue Galois group (`Ideal.Quotient.stabilizerHom_surjective`), and no higher ramification groups and no tame character. An alternative route: the Frobenius relation and commutativity give $\sigma^{q-1} = 1$ on the tame quotient, and the tame inertia group is cyclic.
-- source:
--   The ramification-theoretic proof of the Kronecker-Weber theorem: L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Chapter 14 (cited by chapter); M. J. Greenberg, An elementary proof of the Kronecker-Weber theorem, Amer. Math. Monthly 81 (1974). The tame character $\sigma \mapsto \sigma(\pi)/\pi$ is standard.

import Mathlib

open NumberField

theorem NumberField.exists_injective_inertia_monoidHom_zmod_units (K : Type*) [Field K]
    [NumberField K] [IsAbelianGalois ℚ K] (q : ℕ) (hq : q.Prime) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span {(q : ℤ)})] (h : ¬ q ∣ Nat.card (Q.inertia (K ≃ₐ[ℚ] K))) :
    ∃ f : Q.inertia (K ≃ₐ[ℚ] K) →* (ZMod q)ˣ, Function.Injective f := by sorry
